import Zcash.Snark.ZeroKnowledge.DensePolynomial
import Zcash.Snark.ZeroKnowledge.MultiopenIpa

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- Materialized data carried from opening-group construction into the real multi-opening and IPA. -/
structure StoredOpeningGroup where
  coefficients : List Fp
  points : List Fp
  blind : Fp

/-- Semantic interpretation of stored opening data; execution uses the lists directly. -/
def StoredOpeningGroup.erase (group : StoredOpeningGroup) : BlindedOpeningGroup where
  polynomial := densePolynomial group.coefficients
  points := group.points
  blind := group.blind

end Zcash.Snark.ZeroKnowledge
