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

/-- Agreement on every scheduled receive determines the entire typed challenge record. -/
theorem plonkAttemptChallenge_prefix_injective {k : ℕ} (left right : Challenges k Fp)
    (h : ∀ i < 11 + k, plonkAttemptChallenge left i = plonkAttemptChallenge right i) :
    left = right := by
  have htheta : left.theta = right.theta := h 0 (by omega)
  have hbeta : left.beta = right.beta := h 1 (by omega)
  have hgamma : left.gamma = right.gamma := h 2 (by omega)
  have hy : left.y = right.y := h 3 (by omega)
  have hx : left.x = right.x := h 4 (by omega)
  have hx1 : left.x1 = right.x1 := h 5 (by omega)
  have hx2 : left.x2 = right.x2 := h 6 (by omega)
  have hx3 : left.x3 = right.x3 := h 7 (by omega)
  have hx4 : left.x4 = right.x4 := h 8 (by omega)
  have hxi : left.xi = right.xi := h 9 (by omega)
  have hz : left.z = right.z := h 10 (by omega)
  have hrounds : left.ipaRound = right.ipaRound := by
    funext j
    simpa only [plonkAttemptChallenge_round] using h (11 + j.val) (by omega)
  cases left
  cases right
  congr

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
