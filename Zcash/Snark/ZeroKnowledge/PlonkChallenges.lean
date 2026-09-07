import Zcash.Snark.Core.Challenges
import Zcash.Snark.ZeroKnowledge.PlonkTranscript

/-!
# Full interactive verifier challenge tapes

The `11 + k` challenge values are ordered as in the verifier: `theta`, `beta`, `gamma`,
`y`, `x`, the four multiopen challenges, `xi`, `z`, and the IPA round challenges.
These laws sample an independent tape; they do not describe Fiat–Shamir hashing.
The sufficient conditions below record only the exclusions used by the joint simulator.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf)
open Zcash.Common
open scoped ENNReal

/-- The whole verifier tape, including challenges unused after a possible failure. -/
abbrev PlonkChallengeTape (k : ℕ) (F : Type*) := Fin (k + 11) → F

/-- Decode independent field coins in the existing verifier's challenge order. -/
def plonkChallengesFromTape {k : ℕ} {F : Type*}
    (tape : PlonkChallengeTape k F) : Challenges k F where
  theta := tape ⟨0, by omega⟩
  beta := tape ⟨1, by omega⟩
  gamma := tape ⟨2, by omega⟩
  y := tape ⟨3, by omega⟩
  x := tape ⟨4, by omega⟩
  x1 := tape ⟨5, by omega⟩
  x2 := tape ⟨6, by omega⟩
  x3 := tape ⟨7, by omega⟩
  x4 := tape ⟨8, by omega⟩
  xi := tape ⟨9, by omega⟩
  z := tape ⟨10, by omega⟩
  ipaRound := fun j => tape ⟨11 + j.val, by omega⟩

/-- Sufficient public challenge conditions for the joint algebraic simulation. -/
def PlonkChallengesGood {k : ℕ} (ch : Challenges k Fp) : Prop :=
  ch.xi ≠ 0 ∧ (∀ j, ch.ipaRound j ≠ 0) ∧ ch.x ^ 2048 ≠ 1 ∧
    Function.Injective (plonkObservationPoints (omegaOf 11) ch.x ch.x3) ∧
      ∀ i : Fin 5, ∀ j : Fin 2048,
        plonkObservationPoints (omegaOf 11) ch.x ch.x3 i ≠ omegaOf 11 ^ j.val

/-- Independent exactly uniform field challenges. -/
noncomputable def uniformPlonkChallenges (k : ℕ) : PMF (Challenges k Fp) :=
  (PMF.uniformOfFintype (PlonkChallengeTape k Fp)).map plonkChallengesFromTape

/-- Independent verifier challenges using the implemented wide-reduction law. -/
noncomputable def widePlonkChallenges (k : ℕ) : PMF (Challenges k Fp) :=
  (sampleFieldsWith (k + 11) plonkChallengesFromTape).runFreshPMF fieldSample

/-- The evaluation challenge has exactly the wide-reduced field law in the complete tape. -/
theorem widePlonkChallenges_x (k : ℕ) :
    (widePlonkChallenges k).map (fun ch => ch.x) = fieldSample := by
  rw [widePlonkChallenges, ← sampleFieldsWith_map]
  exact sampleFieldsWith_coordinate (k + 11) ⟨4, by omega⟩ fieldSample

/-- The corresponding coordinate is exactly uniform under the ideal verifier tape law. -/
theorem uniformPlonkChallenges_x (k : ℕ) :
    (uniformPlonkChallenges k).map (fun ch => ch.x) = idealFieldSample := by
  rw [uniformPlonkChallenges, PMF.map_comp, ← sampleFieldsWith_uniform]
  exact sampleFieldsWith_coordinate (k + 11) ⟨4, by omega⟩ idealFieldSample

/-- Replacing the complete verifier tape by uniform field coins costs `k+11` sample biases. -/
theorem widePlonkChallenges_sampling_error_bound (k : ℕ) :
    PMFEventBiasLE (widePlonkChallenges k) (uniformPlonkChallenges k)
        (((k + 11 : ℕ) : ℝ≥0∞) * challenge255Bias) ∧
      PMFEventBiasLE (uniformPlonkChallenges k) (widePlonkChallenges k)
        (((k + 11 : ℕ) : ℝ≥0∞) * challenge255Bias) :=
  sampleFieldsWith_error_bound (k + 11) plonkChallengesFromTape

end Zcash.Snark.ZeroKnowledge
