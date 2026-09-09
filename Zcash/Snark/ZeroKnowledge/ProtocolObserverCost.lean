import Zcash.Snark.ZeroKnowledge.ProverAttempt
import Zcash.Snark.ZeroKnowledge.TranscriptAbsorbCost

/-!
# Counted observation of the original complete attempt

The observer stops at the original point-encoding and post-challenge failures.
Its cost retains every codec, check, received challenge, copied byte, and result
constructor that is actually executed. Complete transcript production is charged
separately by the caller, including messages after an early stop.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Observe the original schedule while retaining every executed producer cost. -/
def observeProtocolTraceCosted {G : Type*}
    (pointCodec : G → Option (List UInt8) × ℕ) (scalarCodec : Fp → List UInt8 × ℕ)
    (challenges : ℕ → Fp × ℕ) (afterChallenge : ℕ → Option ProverAttemptFailure × ℕ) :
    ℕ → List (TranscriptElt Fp G) → ProverAttemptResult × ℕ
  | _, [] => (⟨[], [], .complete⟩, 1)
  | next, .point point :: rest =>
    let encoded := pointCodec point
    match encoded.1 with
    | none => (⟨[], [], .failed .retryRandomness⟩, encoded.2 + 8)
    | some bytes =>
      let result := observeProtocolTraceCosted pointCodec scalarCodec challenges afterChallenge next rest
      let joined := appendListCosted bytes result.1.proof
      (⟨joined.1, result.1.received, result.1.status⟩, encoded.2 + result.2 + joined.2 + 8)
  | next, .scalar scalar :: rest =>
    let encoded := scalarCodec scalar
    let result := observeProtocolTraceCosted pointCodec scalarCodec challenges afterChallenge next rest
    let joined := appendListCosted encoded.1 result.1.proof
    (⟨joined.1, result.1.received, result.1.status⟩, encoded.2 + result.2 + joined.2 + 8)
  | next, .challenge :: rest =>
    let checked := afterChallenge next
    let received := challenges next
    match checked.1 with
    | some reason => (⟨[], [received.1], .failed reason⟩, checked.2 + received.2 + 8)
    | none =>
      let result := observeProtocolTraceCosted pointCodec scalarCodec challenges afterChallenge (next + 1) rest
      (⟨result.1.proof, received.1 :: result.1.received, result.1.status⟩,
        checked.2 + received.2 + result.2 + 8)

/-- All proof bytes, received challenges, and stopping statuses equal the original observer. -/
theorem observeProtocolTraceCosted_result {G : Type*}
    (pointCodec : G → Option (List UInt8) × ℕ) (scalarCodec : Fp → List UInt8 × ℕ)
    (challenges : ℕ → Fp × ℕ) (afterChallenge : ℕ → Option ProverAttemptFailure × ℕ)
    (next : ℕ) (trace : List (TranscriptElt Fp G)) :
    (observeProtocolTraceCosted pointCodec scalarCodec challenges afterChallenge next trace).1 =
      observeProtocolTrace (fun point => (pointCodec point).1) (fun scalar => (scalarCodec scalar).1)
        (fun index => (challenges index).1) (fun index => (afterChallenge index).1) next trace := by
  induction trace generalizing next with
  | nil => rfl
  | cons item rest ih =>
    cases item with
    | point point =>
      cases h : (pointCodec point).1 <;>
        simp only [observeProtocolTraceCosted, observeProtocolTrace, h, appendListCosted_result, ih]
    | scalar scalar =>
      simp only [observeProtocolTraceCosted, observeProtocolTrace, appendListCosted_result, ih]
    | challenge =>
      cases h : (afterChallenge next).1 <;>
        simp only [observeProtocolTraceCosted, observeProtocolTrace, h, ih]

/-- A complete bound covers every stopping branch without assuming successful encoding. -/
theorem observeProtocolTraceCosted_cost_le {G : Type*}
    (pointCodec : G → Option (List UInt8) × ℕ) (scalarCodec : Fp → List UInt8 × ℕ)
    (challenges : ℕ → Fp × ℕ) (afterChallenge : ℕ → Option ProverAttemptFailure × ℕ)
    (encoding width challengePrice checkPrice : ℕ)
    (hpoint : ∀ point, (pointCodec point).2 ≤ encoding)
    (hpointWidth : ∀ point bytes, bytes ∈ (pointCodec point).1 → bytes.length ≤ width)
    (hscalar : ∀ scalar, (scalarCodec scalar).2 ≤ encoding)
    (hscalarWidth : ∀ scalar, (scalarCodec scalar).1.length ≤ width)
    (hchallenge : ∀ index, (challenges index).2 ≤ challengePrice)
    (hcheck : ∀ index, (afterChallenge index).2 ≤ checkPrice)
    (next : ℕ) (trace : List (TranscriptElt Fp G)) :
    (observeProtocolTraceCosted pointCodec scalarCodec challenges afterChallenge next trace).2 ≤
      trace.length * (encoding + width + challengePrice + checkPrice + 16) + 1 := by
  induction trace generalizing next with
  | nil => simp only [observeProtocolTraceCosted, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons item rest ih =>
    have hrest := ih next
    cases item with
    | point point =>
      have hp := hpoint point
      cases h : (pointCodec point).1 with
      | none =>
        simp only [observeProtocolTraceCosted, h, List.length_cons]
        nlinarith only [hp]
      | some bytes =>
        have hb := hpointWidth point bytes (by simp [h])
        simp only [observeProtocolTraceCosted, h, appendListCosted_cost, List.length_cons]
        nlinarith only [hp, hb, hrest]
    | scalar scalar =>
      have hs := hscalar scalar
      have hb := hscalarWidth scalar
      simp only [observeProtocolTraceCosted, appendListCosted_cost, List.length_cons]
      nlinarith only [hs, hb, hrest]
    | challenge =>
      have hc := hchallenge next
      have hk := hcheck next
      cases h : (afterChallenge next).1 with
      | none =>
        have hn := ih (next + 1)
        simp only [observeProtocolTraceCosted, h, List.length_cons]
        nlinarith only [hc, hk, hn]
      | some reason =>
        simp only [observeProtocolTraceCosted, h, List.length_cons]
        nlinarith only [hc, hk]

end Zcash.Snark.ZeroKnowledge
