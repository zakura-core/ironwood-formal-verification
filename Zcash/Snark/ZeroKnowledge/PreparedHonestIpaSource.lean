import Zcash.Snark.ZeroKnowledge.PreparedHonestIpaCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp URS)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The prepared real IPA uses exactly the original computed multi-opening, for every challenge. -/
theorem preparedHonestIpaCosted_computed (costs : FieldOperationCosts)
    (groupAdd groupScale equal read omegaAccess : ℕ)
    (generators : Fin 2048 → G × ℕ) (W U : G × ℕ)
    (x2 x4 q quotientBlind xi z : Fp × ℕ) (groups : List StoredOpeningGroup)
    (rounds : Fin 11 → Fp × ℕ) (tape : Fin (ipaSampleCount 11) → Fp × ℕ)
    (hpoints : ∀ group ∈ groups, group.points.length ≤ 4) :
    (preparedHonestIpaCosted costs groupAdd groupScale equal read generators W U
      (storedMultiopenDataCosted costs equal read omegaAccess x2 x4 q quotientBlind groups)
      q xi z rounds tape).1 =
      materializedIpaTranscript (ipaTranscriptFromTape
        (computedMultiopenIpaPublic
          ({ k := 11, g := fun i => (generators i).1, w := W.1, u := U.1 } : URS G)
          x2.1 x4.1 q.1 xi.1 z.1 quotientBlind.1 (fun i => (rounds i).1)
          (groups.map StoredOpeningGroup.erase))
        (Zcash.Snark.ZeroKnowledge.polynomialCoefficients 2048
          (multiopenFinalPolynomial x2.1 x4.1 (groups.map StoredOpeningGroup.erase)))
        (multiopenFinalBlind x4.1 quotientBlind.1 (groups.map StoredOpeningGroup.erase))
        (fun i => (tape i).1)) := by
  let urs : URS G := { k := 11, g := fun i => (generators i).1, w := W.1, u := U.1 }
  rewrite [preparedHonestIpaCosted_result,
    storedMultiopenDataCosted_polynomial_result costs equal read omegaAccess x2 x4 q quotientBlind groups hpoints,
    storedMultiopenDataCosted_blind_result,
    storedMultiopenDataCosted_value_result costs equal read omegaAccess urs]
  simp only [computedMultiopenIpaPublic, IpaPublic.ofMsm, computedMultiopenOpening_commitment]
  rfl

end Zcash.Snark.ZeroKnowledge
