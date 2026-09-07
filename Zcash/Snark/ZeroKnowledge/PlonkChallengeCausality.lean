import Zcash.Snark.ZeroKnowledge.ProtocolCausality
import Zcash.Snark.ZeroKnowledge.PlonkAttempt

/-!
# The specified attempt checks use only received challenges

The duplicate-opening check reads `x` after `x1,x2`, and the IPA retry check
reads its current round challenge. Both therefore satisfy the same prefix
causality condition as an interactive prover. Combined with a causal message
producer, this proves causality of every encoded prefix, including failures.

The message-producer condition remains explicit in the generic adapter below.
It must be proved for the complete reference construction separately.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The actual exceptional-case checks never read an unseen verifier challenge. -/
theorem plonkAfterChallenge_causal {k : ℕ} :
    ProtocolChecksCausal (plonkAttemptChallenge (k := k)) plonkAfterChallenge := by
  intro left right index h
  by_cases hindex : index = 6
  · subst index
    have hx : left.x = right.x := h 4 (by decide)
    simp [plonkAfterChallenge, hx]
  · simp only [plonkAfterChallenge, hindex, false_and, if_false, h index le_rfl]

/-- A causal typed-proof producer remains causal through the existing codecs and stopping checks. -/
theorem plonkProtocolCausal_observation {actions k : ℕ} {G : Type*}
    (pointCodec : G → Option (List UInt8)) (scalarCodec : Fp → List UInt8)
    (produce : Challenges k Fp → ProofString (plonkProofShape actions k) Fp G)
    (hproduce : ProtocolCausal plonkAttemptChallenge (fun ch => plonkAttemptTrace (produce ch)))
    (n : ℕ) (left right : Challenges k Fp)
    (hcoins : ∀ i < n, plonkAttemptChallenge left i = plonkAttemptChallenge right i) :
    observeProtocolTrace pointCodec scalarCodec (plonkAttemptChallenge left) (plonkAfterChallenge left) 0
        (protocolPrefix n (plonkAttemptTrace (produce left))) =
      observeProtocolTrace pointCodec scalarCodec (plonkAttemptChallenge right) (plonkAfterChallenge right) 0
        (protocolPrefix n (plonkAttemptTrace (produce right))) :=
  protocolCausal_observation pointCodec scalarCodec plonkAttemptChallenge plonkAfterChallenge
    (fun ch => plonkAttemptTrace (produce ch)) hproduce plonkAfterChallenge_causal n left right hcoins

end Zcash.Snark.ZeroKnowledge
