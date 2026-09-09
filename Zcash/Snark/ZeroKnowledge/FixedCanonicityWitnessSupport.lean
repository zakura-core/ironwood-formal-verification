import Zcash.Snark.ZeroKnowledge.WitnessFunctionSupport
import Zcash.Circuits.Ecc.MulFixed.BaseFieldElem
import Zcash.Circuits.Ecc.MulFixed.Short

/-!
# Read certificates for the original fixed-base canonicity witnesses

The arithmetic and conditional negation are deterministic functions of the
listed source cells. No range, sign, curve, or successful-witness premise is used.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits
open Zcash.Circuits.Ecc

/-- The canonicity offset reads the scalar and its high running-sum cell. -/
theorem mulFixed_alphaZeroPrimeWit_support (alpha high : AssignedCell Fp) :
    WitnessFunctionSupport [alpha, high]
      (fun env => ((MulFixed.BaseFieldElem.alphaZeroPrimeWit alpha high).eval env)[0]) :=
  ((witnessFunctionSupport_readCell alpha).pair (witnessFunctionSupport_readCell high)).map
    (fun values => values.1 - values.2 * ((2 ^ 252 : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) - tP)

/-- The two high scalar bits need only the original scalar cell. -/
theorem mulFixed_alpha1Wit_support (alpha : AssignedCell Fp) :
    WitnessFunctionSupport [alpha]
      (fun env => ((MulFixed.BaseFieldElem.alpha1Wit alpha).eval env)[0]) :=
  (witnessFunctionSupport_readCell alpha).map (fun value => ((value.val / 2 ^ 252 % 4 : ℕ) : Fp))

/-- The top scalar bit likewise needs only the original scalar cell. -/
theorem mulFixed_alpha2Wit_support (alpha : AssignedCell Fp) :
    WitnessFunctionSupport [alpha]
      (fun env => ((MulFixed.BaseFieldElem.alpha2Wit alpha).eval env)[0]) :=
  (witnessFunctionSupport_readCell alpha).map (fun value => ((value.val / 2 ^ 254 % 2 : ℕ) : Fp))

/-- The short-scalar final y-coordinate depends on the sign and unsigned result. -/
theorem mulFixed_yVarWit_support (sign y : AssignedCell Fp) :
    WitnessFunctionSupport [sign, y] (fun env => ((MulFixed.Short.yVarWit sign y).eval env)[0]) :=
  ((witnessFunctionSupport_readCell sign).pair (witnessFunctionSupport_readCell y)).map
    (fun values => if values.1 = -1 then -values.2 else values.2)

end Zcash.Snark.ZeroKnowledge
