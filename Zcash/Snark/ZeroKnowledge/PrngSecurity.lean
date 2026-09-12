import Zcash.Snark.ZeroKnowledge.BooleanBias
import Zcash.Snark.ZeroKnowledge.PrngReduction

/-!
# A concrete PRNG security game with independent auxiliary data

One seed consists of `seedBits` independent uniform bits. The output type fixes
the complete generated tape. Auxiliary data is sampled before and independently
of the seed, and both games give that data and one candidate tape to the same
randomized Boolean test.

`UniformSeedPrngSecure` quantifies only over the supplied admissible class. A
computational instantiation must justify that class, for example with a checked
running-time budget, and prove that the actual reduction belongs to it. No
efficiency or PRNG security assertion follows from defining this predicate.
The advantage is the difference of acceptance probabilities, expressed as two
inequalities; it is not statistical distance between the whole output tapes.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Common
open scoped ENNReal

/-- One complete generated tape from one fresh uniform bit seed. -/
noncomputable def uniformSeedTapeSource {Tape : Type*} (seedBits : ℕ)
    (generate : (Fin seedBits → Bool) → Tape) : PMF Tape :=
  seededTapeSource (PMF.uniformOfFintype (Fin seedBits → Bool)) generate

/-- The auxiliary data and candidate tape are sampled independently, then tested together. -/
noncomputable def auxiliaryPrngGame {Aux Tape : Type*} (auxiliary : PMF Aux)
    (source : PMF Tape) (test : Aux → Tape → PMF Bool) : PMF Bool :=
  auxiliary.bind fun aux => source.bind (test aux)

/-- The generated game is exactly fresh uniform seed sampling after the auxiliary data. -/
theorem auxiliaryPrngGame_seed_law {Aux Tape : Type*} (auxiliary : PMF Aux)
    (seedBits : ℕ) (generate : (Fin seedBits → Bool) → Tape)
    (test : Aux → Tape → PMF Bool) :
    auxiliaryPrngGame auxiliary (uniformSeedTapeSource seedBits generate) test =
      auxiliary.bind (fun aux => (PMF.uniformOfFintype (Fin seedBits → Bool)).bind
        (fun seed => test aux (generate seed))) := by
  simp only [auxiliaryPrngGame, uniformSeedTapeSource, seededTapeSource,
    PMF.bind_map, Function.comp_def]

/-- Concrete security for an explicit class of tests, output type, independent auxiliary law, and seed length. -/
def UniformSeedPrngSecure {Aux Tape : Type*} [Fintype Tape] [Nonempty Tape]
    (seedBits : ℕ) (generate : (Fin seedBits → Bool) → Tape) (auxiliary : PMF Aux)
    (admissible : Set (Aux → Tape → PMF Bool)) (advantage : ℝ≥0∞) : Prop :=
  ∀ test ∈ admissible,
    (auxiliaryPrngGame auxiliary (uniformSeedTapeSource seedBits generate) test) true ≤
        (auxiliaryPrngGame auxiliary (PMF.uniformOfFintype Tape) test) true + advantage ∧
      (auxiliaryPrngGame auxiliary (PMF.uniformOfFintype Tape) test) true ≤
        (auxiliaryPrngGame auxiliary (uniformSeedTapeSource seedBits generate) test) true + advantage

/-- Applying the security game to an admissible test bounds its Boolean output law in both directions. -/
theorem uniformSeedPrngSecure_event_bias {Aux Tape : Type*} [Fintype Tape] [Nonempty Tape]
    {seedBits : ℕ} {generate : (Fin seedBits → Bool) → Tape} {auxiliary : PMF Aux}
    {admissible : Set (Aux → Tape → PMF Bool)} {advantage : ℝ≥0∞}
    (secure : UniformSeedPrngSecure seedBits generate auxiliary admissible advantage)
    {test : Aux → Tape → PMF Bool} (hclass : test ∈ admissible) :
    PMFEventBiasLE (auxiliaryPrngGame auxiliary (uniformSeedTapeSource seedBits generate) test)
        (auxiliaryPrngGame auxiliary (PMF.uniformOfFintype Tape) test) advantage ∧
      PMFEventBiasLE (auxiliaryPrngGame auxiliary (PMF.uniformOfFintype Tape) test)
        (auxiliaryPrngGame auxiliary (uniformSeedTapeSource seedBits generate) test) advantage :=
  boolean_event_bias_iff.mpr (secure test hclass)

end Zcash.Snark.ZeroKnowledge
