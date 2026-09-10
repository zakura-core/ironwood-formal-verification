import Zcash.Snark.ZeroKnowledge.PlonkEncoding

/-!
# The released Orchard proof-call observation

The caller receives proof bytes, a returned error, or a panic. Failed calls do
not return the partial proof buffer and do not retry. The reference observer
retains the terminal failure reason and the error's position in the schedule.

## Source connection

Common `50f712ee22ca95e2dd5230c6f331ce2e433d70ee` checks duplicate queries after
`x1,x2`, and unwraps each IPA round challenge's inverse. `plonk::create_proof`
maps multi-opening I/O failures to `Error::Opening`; earlier point failures are
`Error::Transcript`. `PROVENANCE.md` records the source paths. Agreement with
the Rust execution remains an explicit implementation trust boundary.
-/

namespace Zcash.Snark.ZeroKnowledge.Zakura

open Zcash.Arithmetic (Fp)

/-- Returned errors arising on the modeled, version-matched Orchard proof path. -/
inductive AttemptError where
  | transcript
  | opening
  deriving DecidableEq

/-- The single proof call exposes no partial proof bytes when it fails. -/
inductive AttemptOutcome where
  | proof (bytes : List UInt8)
  | error (reason : AttemptError)
  | panic
  deriving DecidableEq

/-- A stopped reference attempt determines the released API's observable result.

The zero-IPA failure denotes the released inverse-unwrap panic. The first
multi-opening point follows the seventh receive, determining whether an
identity point is returned as an opening error or a transcript error.
-/
def observeAttempt (attempt : ProverAttemptResult) : AttemptOutcome :=
  match attempt.status with
  | .complete => .proof attempt.proof
  | .failed .coincidentOpeningQueries => .error .opening
  | .failed .zeroIpaChallenge => .panic
  | .failed .identityPoint =>
    if 7 ≤ attempt.received.length then .error .opening
    else .error .transcript

/-- A completed reference attempt returns its exact encoded proof buffer. -/
theorem observeAttempt_complete (bytes : List UInt8) (received : List Fp) :
    observeAttempt ⟨bytes, received, .complete⟩ = .proof bytes := rfl

/-- Duplicate opening queries produce the opening error, independently of the retained prefix. -/
theorem observeAttempt_duplicate (bytes : List UInt8) (received : List Fp) :
    observeAttempt ⟨bytes, received, .failed .coincidentOpeningQueries⟩ = .error .opening := rfl

/-- The terminal zero-IPA failure exposes the released panic outcome. -/
theorem observeAttempt_zeroIpa (bytes : List UInt8) (received : List Fp) :
    observeAttempt ⟨bytes, received, .failed .zeroIpaChallenge⟩ = .panic := rfl

/-- An identity point before multi-opening returns the transcript error. -/
theorem observeAttempt_earlyIdentity (bytes : List UInt8) (received : List Fp)
    (hearly : received.length < 7) :
    observeAttempt ⟨bytes, received, .failed .identityPoint⟩ = .error .transcript := by
  have hopening : ¬7 ≤ received.length := by omega
  simp only [observeAttempt, hopening, ↓reduceIte]

/-- An identity point during multi-opening returns the opening error. -/
theorem observeAttempt_openingIdentity (bytes : List UInt8) (received : List Fp)
    (hopening : 7 ≤ received.length) :
    observeAttempt ⟨bytes, received, .failed .identityPoint⟩ = .error .opening := by
  simp only [observeAttempt, hopening, ↓reduceIte]

/-- Public transcript initialization accepts exactly the points that the released writer can encode. -/
def acceptsPublicPrefix (initial : List (TranscriptElt Fp VestaG)) : Bool :=
  initial.all fun element => match element with
    | .point point => decide (point ≠ 0)
    | .scalar _ => true
    | .challenge => true

/-- The public prefix passes exactly when each of its point commitments is nonidentity. -/
theorem acceptsPublicPrefix_iff (initial : List (TranscriptElt Fp VestaG)) :
    acceptsPublicPrefix initial = true ↔
      ∀ point, TranscriptElt.point point ∈ initial → point ≠ 0 := by
  simp only [acceptsPublicPrefix, List.all_eq_true]
  constructor
  · intro h point hmem
    simpa only [decide_eq_true_eq] using h (.point point) hmem
  · intro h element hmem
    cases element with
    | point point => simpa only [decide_eq_true_eq] using h point hmem
    | scalar scalar => rfl
    | challenge => rfl

end Zcash.Snark.ZeroKnowledge.Zakura
