import Zcash.Snark.Verifier.FiatShamir

/-!
# Observing a prover attempt in transcript order

The existing transcript markers determine when a fresh verifier coin is received.
Point encoding can request new randomness before emitting any bytes for that point.
The supplied post-challenge check can stop an attempt after receiving a challenge.
The observer retains the emitted prefix and the challenges actually received.

This interpreter does not hash the transcript. Its challenge tape and checks describe
an interactive experiment; the PLONK module instantiates their fixed schedule.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The two failure cases specified for the prover's message schedule. -/
inductive ProverAttemptFailure where
  | retryRandomness
  | coincidentOpeningQueries
  deriving DecidableEq

/-- Completion is distinct from a request for new randomness and a terminal error. -/
inductive ProverAttemptStatus where
  | complete
  | failed (reason : ProverAttemptFailure)
  deriving DecidableEq

/-- All observable output of one attempt, including an unsuccessful prefix. -/
structure ProverAttemptResult where
  proof : List UInt8
  received : List Fp
  status : ProverAttemptStatus

/-- Count the verifier's challenge markers, independently of the proof's values. -/
def protocolChallengeCount {F G : Type*} : List (TranscriptElt F G) → ℕ
  | [] => 0
  | .challenge :: rest => 1 + protocolChallengeCount rest
  | _ :: rest => protocolChallengeCount rest

/-- Count proof elements; challenge markers have no proof bytes. -/
def protocolMessageCount {F G : Type*} : List (TranscriptElt F G) → ℕ
  | [] => 0
  | .challenge :: rest => protocolMessageCount rest
  | _ :: rest => 1 + protocolMessageCount rest

/-- Concatenating transcript stages adds their challenge counts. -/
@[simp] theorem protocolChallengeCount_append {F G : Type*}
    (left right : List (TranscriptElt F G)) :
    protocolChallengeCount (left ++ right) =
      protocolChallengeCount left + protocolChallengeCount right := by
  induction left with
  | nil => simp [protocolChallengeCount]
  | cons elt left ih => cases elt <;> simp [protocolChallengeCount, ih, Nat.add_assoc]

/-- A stage has no challenges exactly when it contains no challenge marker. -/
theorem protocolChallengeCount_eq_zero_iff {F G : Type*} (trace : List (TranscriptElt F G)) :
    protocolChallengeCount trace = 0 ↔ .challenge ∉ trace := by
  induction trace with
  | nil => simp [protocolChallengeCount]
  | cons elt trace ih => cases elt <;> simp [protocolChallengeCount, ih]

/-- Concatenating transcript stages adds their proof-element counts. -/
@[simp] theorem protocolMessageCount_append {F G : Type*}
    (left right : List (TranscriptElt F G)) :
    protocolMessageCount (left ++ right) = protocolMessageCount left + protocolMessageCount right := by
  induction left with
  | nil => simp [protocolMessageCount]
  | cons elt left ih => cases elt <;> simp [protocolMessageCount, ih, Nat.add_assoc]

/-- Flattening a sequence of stages sums their challenge counts. -/
@[simp] theorem protocolChallengeCount_flatten {F G : Type*}
    (stages : List (List (TranscriptElt F G))) :
    protocolChallengeCount stages.flatten = (stages.map protocolChallengeCount).sum := by
  induction stages with
  | nil => rfl
  | cons stage stages ih => simp [ih]

/-- Read the existing transcript schedule, stopping at the first encoding or challenge failure. -/
def observeProtocolTrace {G : Type*} (pointCodec : G → Option (List UInt8))
    (scalarCodec : Fp → List UInt8) (challenges : ℕ → Fp)
    (afterChallenge : ℕ → Option ProverAttemptFailure) :
    ℕ → List (TranscriptElt Fp G) → ProverAttemptResult
  | _, [] => ⟨[], [], .complete⟩
  | next, .point point :: rest =>
    match pointCodec point with
    | none => ⟨[], [], .failed .retryRandomness⟩
    | some bytes =>
      let result := observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next rest
      ⟨bytes ++ result.proof, result.received, result.status⟩
  | next, .scalar scalar :: rest =>
    let result := observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next rest
    ⟨scalarCodec scalar ++ result.proof, result.received, result.status⟩
  | next, .challenge :: rest =>
    match afterChallenge next with
    | some reason => ⟨[], [challenges next], .failed reason⟩
    | none =>
      let result := observeProtocolTrace pointCodec scalarCodec challenges afterChallenge (next + 1) rest
      ⟨result.proof, challenges next :: result.received, result.status⟩

private theorem challenge_checks_succ (check : ℕ → Option ProverAttemptFailure) (next n : ℕ) :
    (∀ j < 1 + n, check (next + j) = none) ↔
      check next = none ∧ ∀ j < n, check (next + 1 + j) = none := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by omega), ?_⟩
    intro j hj
    simpa only [Nat.add_assoc, Nat.add_comm 1 j] using h (j + 1) (by omega)
  · rintro ⟨hzero, hsucc⟩ j hj
    cases j with
    | zero => simpa using hzero
    | succ j =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 j] using hsucc j (by omega)

/-- An attempt completes exactly when every point encodes and every scheduled check passes. -/
theorem observeProtocolTrace_complete_iff {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (challenges : ℕ → Fp) (afterChallenge : ℕ → Option ProverAttemptFailure)
    (next : ℕ) (trace : List (TranscriptElt Fp G)) :
    (observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next trace).status = .complete ↔
      (∀ point, .point point ∈ trace → pointCodec point ≠ none) ∧
        ∀ j < protocolChallengeCount trace, afterChallenge (next + j) = none := by
  induction trace generalizing next with
  | nil => simp [observeProtocolTrace, protocolChallengeCount]
  | cons elt trace ih =>
    cases elt with
    | point point =>
      cases hp : pointCodec point <;>
        simp [observeProtocolTrace, hp, protocolChallengeCount, ih]
    | scalar scalar =>
      simpa [observeProtocolTrace, protocolChallengeCount] using ih next
    | challenge =>
      cases hc : afterChallenge next <;>
        simp [observeProtocolTrace, hc, protocolChallengeCount, challenge_checks_succ, ih, and_comm]

/-- Once a prefix fails, appending any future transcript leaves the observation unchanged. -/
theorem observeProtocolTrace_append_of_failed {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (challenges : ℕ → Fp) (afterChallenge : ℕ → Option ProverAttemptFailure)
    (next : ℕ) (headTrace tailTrace : List (TranscriptElt Fp G))
    (hfailed : (observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next headTrace).status ≠ .complete) :
    observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next (headTrace ++ tailTrace) =
      observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next headTrace := by
  induction headTrace generalizing next with
  | nil => simp [observeProtocolTrace] at hfailed
  | cons elt headTrace ih =>
    cases elt with
    | point point =>
      cases hp : pointCodec point with
      | none => simp [observeProtocolTrace, hp]
      | some bytes =>
        have hrest := ih next (by simpa [observeProtocolTrace, hp] using hfailed)
        simp only [List.cons_append, observeProtocolTrace, hp, hrest]
    | scalar scalar =>
      have hrest := ih next hfailed
      simp only [List.cons_append, observeProtocolTrace, hrest]
    | challenge =>
      cases hc : afterChallenge next with
      | some reason => simp [observeProtocolTrace, hc]
      | none =>
        have hrest := ih (next + 1) (by simpa [observeProtocolTrace, hc] using hfailed)
        simp only [List.cons_append, observeProtocolTrace, hc, hrest]

/-- Even on failure, the received coins are exactly an initial segment of the ordered tape. -/
theorem observeProtocolTrace_received_prefix {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (challenges : ℕ → Fp) (afterChallenge : ℕ → Option ProverAttemptFailure)
    (next : ℕ) (trace : List (TranscriptElt Fp G)) :
    (observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next trace).received =
      (List.range' next
        (observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next trace).received.length).map
          challenges := by
  induction trace generalizing next with
  | nil => simp [observeProtocolTrace]
  | cons elt trace ih =>
    cases elt with
    | point point =>
      cases hp : pointCodec point with
      | none => simp [observeProtocolTrace, hp]
      | some bytes => simpa only [observeProtocolTrace, hp] using ih next
    | scalar scalar => exact ih next
    | challenge =>
      cases hc : afterChallenge next with
      | some reason => simp [observeProtocolTrace, hc]
      | none =>
        simpa only [observeProtocolTrace, hc, List.length_cons, List.range'_succ, List.map_cons,
          List.cons.injEq, true_and] using ih (next + 1)

/-- Completion consumes every challenge marker, with no extra tape reads. -/
theorem observeProtocolTrace_received_length {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (challenges : ℕ → Fp) (afterChallenge : ℕ → Option ProverAttemptFailure)
    (next : ℕ) (trace : List (TranscriptElt Fp G))
    (hcomplete : (observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next trace).status = .complete) :
    (observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next trace).received.length =
      protocolChallengeCount trace := by
  induction trace generalizing next with
  | nil => rfl
  | cons elt trace ih =>
    cases elt with
    | point point =>
      cases hp : pointCodec point with
      | none => simp [observeProtocolTrace, hp] at hcomplete
      | some bytes =>
        simpa only [observeProtocolTrace, hp, protocolChallengeCount] using
          ih next (by simpa [observeProtocolTrace, hp] using hcomplete)
    | scalar scalar => exact ih next hcomplete
    | challenge =>
      cases hc : afterChallenge next with
      | some reason => simp [observeProtocolTrace, hc] at hcomplete
      | none =>
        have hrest := ih (next + 1) (by simpa [observeProtocolTrace, hc] using hcomplete)
        simp only [observeProtocolTrace, hc, List.length_cons, protocolChallengeCount, hrest, Nat.add_comm]

/-- The eventual byte string with unencodable points omitted, used only to state the prefix property. -/
def protocolTraceBytes {G : Type*} (pointCodec : G → Option (List UInt8))
    (scalarCodec : Fp → List UInt8) : List (TranscriptElt Fp G) → List UInt8
  | [] => []
  | .point point :: rest => (pointCodec point).getD [] ++ protocolTraceBytes pointCodec scalarCodec rest
  | .scalar scalar :: rest => scalarCodec scalar ++ protocolTraceBytes pointCodec scalarCodec rest
  | .challenge :: rest => protocolTraceBytes pointCodec scalarCodec rest

/-- Stopping an attempt never emits bytes from after its stopping point. -/
theorem observeProtocolTrace_proof_prefix {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (challenges : ℕ → Fp) (afterChallenge : ℕ → Option ProverAttemptFailure)
    (next : ℕ) (trace : List (TranscriptElt Fp G)) :
    (observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next trace).proof <+:
      protocolTraceBytes pointCodec scalarCodec trace := by
  induction trace generalizing next with
  | nil => exact ⟨[], rfl⟩
  | cons elt trace ih =>
    cases elt with
    | point point =>
      cases hp : pointCodec point with
      | none => simp [observeProtocolTrace, hp]
      | some bytes =>
        obtain ⟨suffix, hsuffix⟩ := ih next
        refine ⟨suffix, ?_⟩
        simpa only [observeProtocolTrace, hp, protocolTraceBytes, Option.getD_some,
          List.append_assoc] using congrArg (bytes ++ ·) hsuffix
    | scalar scalar =>
      obtain ⟨suffix, hsuffix⟩ := ih next
      refine ⟨suffix, ?_⟩
      simpa only [observeProtocolTrace, protocolTraceBytes, List.append_assoc] using
        congrArg (scalarCodec scalar ++ ·) hsuffix
    | challenge =>
      cases hc : afterChallenge next with
      | some reason => simp [observeProtocolTrace, hc]
      | none => simpa only [observeProtocolTrace, hc, protocolTraceBytes] using ih (next + 1)

/-- Successful observation emits the whole encoding, with every challenge marker omitted. -/
theorem observeProtocolTrace_proof_of_complete {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (challenges : ℕ → Fp) (afterChallenge : ℕ → Option ProverAttemptFailure)
    (next : ℕ) (trace : List (TranscriptElt Fp G))
    (hcomplete : (observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next trace).status = .complete) :
    (observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next trace).proof =
      protocolTraceBytes pointCodec scalarCodec trace := by
  induction trace generalizing next with
  | nil => rfl
  | cons elt trace ih =>
    cases elt with
    | point point =>
      cases hp : pointCodec point with
      | none => simp [observeProtocolTrace, hp] at hcomplete
      | some bytes =>
        simpa only [observeProtocolTrace, hp, protocolTraceBytes, Option.getD_some] using
          congrArg (bytes ++ ·) (ih next (by simpa [observeProtocolTrace, hp] using hcomplete))
    | scalar scalar =>
      exact congrArg (scalarCodec scalar ++ ·) (ih next hcomplete)
    | challenge =>
      cases hc : afterChallenge next with
      | some reason => simp [observeProtocolTrace, hc] at hcomplete
      | none =>
        simpa only [observeProtocolTrace, hc, protocolTraceBytes] using
          ih (next + 1) (by simpa [observeProtocolTrace, hc] using hcomplete)

/-- A fixed-width codec gives the expected complete proof length; challenges add no bytes. -/
theorem observeProtocolTrace_proof_length {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (challenges : ℕ → Fp) (afterChallenge : ℕ → Option ProverAttemptFailure)
    (width next : ℕ) (trace : List (TranscriptElt Fp G))
    (hpoint : ∀ point bytes, pointCodec point = some bytes → bytes.length = width)
    (hscalar : ∀ scalar, (scalarCodec scalar).length = width)
    (hcomplete : (observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next trace).status = .complete) :
    (observeProtocolTrace pointCodec scalarCodec challenges afterChallenge next trace).proof.length =
      width * protocolMessageCount trace := by
  induction trace generalizing next with
  | nil => simp [observeProtocolTrace, protocolMessageCount]
  | cons elt trace ih =>
    cases elt with
    | point point =>
      cases hp : pointCodec point with
      | none => simp [observeProtocolTrace, hp] at hcomplete
      | some bytes =>
        have hrest := ih next (by simpa [observeProtocolTrace, hp] using hcomplete)
        simp only [observeProtocolTrace, hp, List.length_append, protocolMessageCount,
          hpoint point bytes hp, hrest, Nat.mul_add, Nat.mul_one]
    | scalar scalar =>
      have hrest := ih next hcomplete
      simp only [observeProtocolTrace, List.length_append, protocolMessageCount,
        hscalar, hrest, Nat.mul_add, Nat.mul_one]
    | challenge =>
      cases hc : afterChallenge next with
      | some reason => simp [observeProtocolTrace, hc] at hcomplete
      | none =>
        simpa only [observeProtocolTrace, hc, protocolMessageCount] using
          ih (next + 1) (by simpa [observeProtocolTrace, hc] using hcomplete)

end Zcash.Snark.ZeroKnowledge
