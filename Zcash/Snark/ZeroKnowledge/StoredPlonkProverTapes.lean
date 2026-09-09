import Zcash.Snark.ZeroKnowledge.StoredBitTapeCost
import Zcash.Snark.ZeroKnowledge.PlonkChallengeReadCost
import Zcash.Snark.ZeroKnowledge.RandomTapeSource
import Zcash.Snark.ZeroKnowledge.PreIpaTapeLists
import Zcash.Snark.ZeroKnowledge.TapeSplitCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
open Zcash.Common

/-- Original real-prover raw words, verifier challenges, and complete private field tape. -/
structure StoredPlonkProverTapes where
  raw : List (Fin challengeDigestCard)
  challenges : Challenges 11 (Fp × ℕ)
  privateFields : List Fp

/-- Produce both correlated representations from the same bits, retaining all preparation work. -/
def storedPlonkProverTapesCosted (actions read : ℕ) (bits : List Bool) : StoredPlonkProverTapes × ℕ :=
  let count := 22 + fieldSampleCount actions
  let raw := storedRawTapeCosted count read bits
  let fields := storedFieldTapeCosted count read bits
  let parts := splitListCosted read 22 fields.1
  let challenges := storedPlonkChallengesCosted 11 read fields.1 0
  (⟨raw.1, challenges.1, parts.1.2⟩, raw.2 + fields.2 + parts.2 + challenges.2 + 4)

/-- Both stored outputs have exactly the original public/private tape capacities. -/
theorem storedPlonkProverTapesCosted_lengths (actions read : ℕ) (bits : List Bool) :
    (storedPlonkProverTapesCosted actions read bits).1.raw.length = 22 + fieldSampleCount actions ∧
      (storedPlonkProverTapesCosted actions read bits).1.privateFields.length = fieldSampleCount actions := by
  constructor
  · exact ofFnCosted_length _
  · change (splitListCosted read 22 (storedFieldTapeCosted (22 + fieldSampleCount actions) read bits).1).1.2.length = _
    rewrite [splitListCosted_result, List.length_drop]
    have h : (storedFieldTapeCosted (22 + fieldSampleCount actions) read bits).1.length =
        22 + fieldSampleCount actions := ofFnCosted_length _
    rewrite [h]
    omega

/-- Raw words retain the exact full little-endian random-bit tape. -/
theorem storedPlonkProverTapesCosted_raw_result (actions read : ℕ)
    (bits : Fin ((22 + fieldSampleCount actions) * 512) → Bool) :
    (storedPlonkProverTapesCosted actions read (List.ofFn bits)).1.raw =
      List.ofFn (rawBitsTapeEquiv (22 + fieldSampleCount actions) bits) :=
  storedRawTapeCosted_encode_result read bits

/-- Every verifier challenge is the reduction of the corresponding original public-prefix word. -/
theorem storedPlonkProverTapesCosted_challenges_result (actions read : ℕ)
    (bits : Fin ((22 + fieldSampleCount actions) * 512) → Bool) :
    let parts := splitTapeEquiv 22 (fieldSampleCount actions) (Fin challengeDigestCard)
      (rawBitsTapeEquiv (22 + fieldSampleCount actions) bits)
    Challenges.eraseCosts (storedPlonkProverTapesCosted actions read (List.ofFn bits)).1.challenges =
      plonkChallengesFromTape (k := 11) (reduceFieldTape parts.1) := by
  let raw := rawBitsTapeEquiv (22 + fieldSampleCount actions) bits
  change Challenges.eraseCosts (storedPlonkChallengesCosted 11 read
    (storedFieldTapeCosted (22 + fieldSampleCount actions) read (List.ofFn bits)).1 0).1 = _
  rewrite [storedPlonkChallengesCosted_result, storedFieldTapeCosted_encode_result]
  apply congrArg (plonkChallengesFromTape (k := 11))
  funext i
  change (List.ofFn (reduceFieldTape raw)).getD (0 + i.val) 0 =
    reduceFieldTape raw (Fin.castAdd (fieldSampleCount actions) i)
  simpa only [getDListCosted_result, Fin.val_castAdd, Nat.zero_add] using
    getDListCosted_ofFn_result read (0 : Fp) (reduceFieldTape raw) (Fin.castAdd (fieldSampleCount actions) i)

/-- The complete private output is the original wide-reduced suffix in exactly the same order. -/
theorem storedPlonkProverTapesCosted_private_result (actions read : ℕ)
    (bits : Fin ((22 + fieldSampleCount actions) * 512) → Bool) :
    let parts := splitTapeEquiv 22 (fieldSampleCount actions) (Fin challengeDigestCard)
      (rawBitsTapeEquiv (22 + fieldSampleCount actions) bits)
    (storedPlonkProverTapesCosted actions read (List.ofFn bits)).1.privateFields =
      List.ofFn (reduceFieldTape parts.2) := by
  change (splitListCosted read 22
    (storedFieldTapeCosted (22 + fieldSampleCount actions) read (List.ofFn bits)).1).1.2 = _
  rewrite [splitListCosted_result, storedFieldTapeCosted_encode_result]
  exact (ofFn_splitTape_right Fp 22 (fieldSampleCount actions) _).symm

end Zcash.Snark.ZeroKnowledge
