import Zcash.Snark.ZeroKnowledge.PlonkQueryGroups

/-!
# The common node labels for verifier and reference opening groups

These small lists identify the same nodes in the verifier's four-label pattern
and the reference simulator's five-observation view. The fifth observation is
the later opening challenge and is not a node of these groups.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The four-label node lists for the five opening groups. -/
def plonkGroupPointLabels : Fin 5 → List (Fin 4) := ![[0], [0, 1], [0, 1, 2], [0, 1, 3], [0, 2]]

/-- Forgetting the finite bound gives the point-index sets computed by the verifier. -/
theorem plonkGroupPointLabels_indices (i : Fin 5) :
    (plonkGroupPointLabels i).map Fin.val = plonkGroupPointIndices i := by
  fin_cases i <;> rfl

/-- Embedding the four labels into the simulator's five observations gives its existing node lists. -/
theorem plonkGroupPointLabels_observations (i : Fin 5) :
    (plonkGroupPointLabels i).map Fin.castSucc = plonkOpeningPointIndices i := by
  fin_cases i <;> rfl

/-- Interpreting the labels gives the reference polynomial opening's field points. -/
theorem plonkGroupPointLabels_nodes (omega x : Fp) (i : Fin 5) :
    (plonkGroupPointLabels i).map (plonkQueryPoint omega x) = plonkOpeningPointSets omega x i := by
  fin_cases i <;>
    simp [plonkGroupPointLabels, plonkQueryPoint, plonkQueryRotation, plonkOpeningPointSets,
      rotateOmega, zpow_ofNat]

/-- No group repeats an abstract node label. -/
theorem plonkGroupPointLabels_nodup (i : Fin 5) : (plonkGroupPointLabels i).Nodup := by
  fin_cases i <;> decide +kernel

/-- Node membership agrees with the verifier's natural-number index classification. -/
theorem plonkGroupPointLabels_mem (i : Fin 5) (point : Fin 4) :
    point ∈ plonkGroupPointLabels i ↔ point.val ∈ plonkGroupPointIndices i := by
  fin_cases i <;> fin_cases point <;> decide +kernel

end Zcash.Snark.ZeroKnowledge
