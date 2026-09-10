import Zcash.Snark.ZeroKnowledge.TranscriptScheduleSize

/-!
# A polynomial cost envelope for the complete message schedule

The common input price bounds each field's entire producer. Optional permutation
claims remain present whenever the original proof contains them. The rounded
constants cover the complete constructor, even when observation later aborts.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Both finite collections and all optional permutation fields are charged. -/
theorem absorbPermSets2Costed_cost_le {F G : Type*} {rows columns : ℕ}
    (sets : Fin rows → Fin columns → PermSetEval (F × ℕ)) (access : ℕ)
    (hread : ∀ row column, permSetReadBound (sets row column) access) :
    (flattenFinCosted (fun row => flattenFinCosted (fun column =>
      absorbPermSetCosted (G := G) (sets row column)))).2 ≤
      rows * (columns * (3 * access + 12) + columns * columns + 3 * columns + 3) +
        rows * rows + 1 := by
  have hrow (row : Fin rows) :
      (flattenFinCosted (fun column => absorbPermSetCosted (G := G) (sets row column))).2 ≤
        columns * (3 * access + 12) + columns * columns + 1 := by
    exact flattenFinCosted_cost_le _ (3 * access + 7) 3
      (fun column => absorbPermSetCosted_cost_le _ access (hread row column))
      (fun column => absorbPermSetCosted_length_le _)
  have hlength (row : Fin rows) :
      (flattenFinCosted (fun column => absorbPermSetCosted (G := G) (sets row column))).1.length ≤
        3 * columns := by
    rw [flattenFinCosted_result, Nat.mul_comm]
    exact length_flatten_ofFn_le _ 3 (fun column => absorbPermSetCosted_length_le _)
  have h := flattenFinCosted_cost_le
    (fun row => flattenFinCosted (fun column => absorbPermSetCosted (G := G) (sets row column)))
    (columns * (3 * access + 12) + columns * columns + 1) (3 * columns) hrow hlength
  convert h using 1
  ring

/-- Every original lookup claim and both collections remain in the matrix cost. -/
theorem absorbLookups2Costed_cost_le {F G : Type*} {rows columns : ℕ}
    (lookups : Fin rows → Fin columns → LookupEval (F × ℕ)) (access : ℕ)
    (hread : ∀ row column, lookupEvalReadBound (lookups row column) access) :
    (flattenFinCosted (fun row => flattenFinCosted (fun column =>
      absorbLookupCosted (G := G) (lookups row column)))).2 ≤
      rows * (columns * (5 * access + 18) + columns * columns + 5 * columns + 3) +
        rows * rows + 1 := by
  have hrow (row : Fin rows) :
      (flattenFinCosted (fun column => absorbLookupCosted (G := G) (lookups row column))).2 ≤
        columns * (5 * access + 18) + columns * columns + 1 := by
    exact flattenFinCosted_cost_le _ (5 * access + 11) 5
      (fun column => absorbLookupCosted_cost_le _ access (hread row column))
      (fun column => le_of_eq (absorbLookupCosted_length _))
  have hlength (row : Fin rows) :
      (flattenFinCosted (fun column => absorbLookupCosted (G := G) (lookups row column))).1.length ≤
        5 * columns := by
    rw [flattenFinCosted_result, Nat.mul_comm]
    exact length_flatten_ofFn_le _ 5 (fun column => le_of_eq (absorbLookupCosted_length _))
  have h := flattenFinCosted_cost_le
    (fun row => flattenFinCosted (fun column => absorbLookupCosted (G := G) (lookups row column)))
    (columns * (5 * access + 18) + columns * columns + 1) (5 * columns) hrow hlength
  convert h using 1
  ring

/-- Produce all actual evaluation claims with their complete field-reader costs. -/
theorem proofEvaluationBlocksCosted_cost_le {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) (F × ℕ) (G × ℕ)) (access : ℕ)
    (hread : ProofFieldReadBound proof access) :
    (proofEvaluationBlocksCosted proof).2 ≤
      4 * actions * actions + 50 * actions * access + 900 * actions + 45 * access + 1300 := by
  have hi := absorbScalars2Costed_cost_le (G := G) proof.instanceEvals access hread.instanceEvals
  have ha := absorbScalars2Costed_cost_le (G := G) proof.adviceEvals access hread.adviceEvals
  have hf := absorbScalarsCosted_cost_le (G := G) proof.fixedEvals access hread.fixedEvals
  have hs := absorbScalarsCosted_cost_le (G := G) proof.permutationCommonEvals access
    hread.permutationCommonEvals
  have hp := absorbPermSets2Costed_cost_le (G := G) proof.permutationSetEvals access
    hread.permutationSetEvals
  have hl := absorbLookups2Costed_cost_le (G := G) proof.lookupEvals access hread.lookupEvals
  have hr := hread.vanishingRandomEval
  have hsize := proofEvaluationBlocksCosted_length_le proof
  have hcost := concatTranscriptBlocksCosted_cost (α := TranscriptElt F G)
    [absorbScalars2Costed proof.instanceEvals,
      absorbScalars2Costed proof.adviceEvals,
      absorbScalarsCosted proof.fixedEvals,
      ([TranscriptElt.scalar proof.vanishingRandomEval.1], proof.vanishingRandomEval.2 + 2),
      absorbScalarsCosted proof.permutationCommonEvals,
      flattenFinCosted (fun action => flattenFinCosted (fun set =>
        absorbPermSetCosted (proof.permutationSetEvals action set))),
      flattenFinCosted (fun action => flattenFinCosted (fun lookup =>
        absorbLookupCosted (proof.lookupEvals action lookup)))]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil] at hcost
  change (proofEvaluationBlocksCosted proof).2 = _ + (proofEvaluationBlocksCosted proof).1.length + _ + _ at hcost
  conv at hi =>
    rhs
    simp only [plonkProofShape, FixtureMax.shape]
  conv at ha =>
    rhs
    simp only [plonkProofShape, FixtureMax.shape]
  conv at hf =>
    rhs
    simp only [plonkProofShape, FixtureMax.shape]
  conv at hs =>
    rhs
    simp only [plonkProofShape, FixtureMax.shape]
  conv at hp =>
    rhs
    simp only [plonkProofShape, FixtureMax.shape]
  conv at hl =>
    rhs
    simp only [plonkProofShape, FixtureMax.shape]
  nlinarith only [hi, ha, hf, hs, hp, hl, hr, hsize, hcost]

/-- The full original pre-IPA schedule has a common polynomial producer bound. -/
theorem preIpaTranscriptCosted_cost_le {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) (F × ℕ) (G × ℕ)) (access : ℕ)
    (hread : ProofFieldReadBound proof access) :
    (preIpaTranscriptCosted proof).2 ≤
      8 * actions * actions + 72 * actions * access + 1200 * actions + 61 * access + 1800 := by
  have ha := absorbPoints2Costed_cost_le (F := F) proof.adviceCommitments access hread.adviceCommitments
  have hl := absorbLookupPermutedCosted_cost_le (F := F)
    proof.lookupPermutedInput proof.lookupPermutedTable access hread.lookupPermutedInput hread.lookupPermutedTable
  have hp := absorbPoints2Costed_cost_le (F := F) proof.permutationProduct access hread.permutationProduct
  have ht := absorbPoints2Costed_cost_le (F := F) proof.lookupProduct access hread.lookupProduct
  have hh := absorbPointsCosted_cost_le (F := F) proof.hPieces access hread.hPieces
  have he := proofEvaluationBlocksCosted_cost_le proof access hread
  have hu := absorbScalarsCosted_cost_le (G := G) proof.multiopenU access hread.multiopenU
  have hr := hread.vanishingRandom
  have hq := hread.multiopenQPrime
  have hs := hread.ipaS
  have hsize := preIpaTranscriptCosted_length_le proof
  have hcost := concatTranscriptBlocksCosted_cost (α := TranscriptElt F G)
    [absorbPoints2Costed proof.adviceCommitments,
      ([TranscriptElt.challenge], 2),
      absorbLookupPermutedCosted proof.lookupPermutedInput proof.lookupPermutedTable,
      ([.challenge, .challenge], 3),
      absorbPoints2Costed proof.permutationProduct,
      absorbPoints2Costed proof.lookupProduct,
      ([.point proof.vanishingRandom.1], proof.vanishingRandom.2 + 2),
      ([.challenge], 2), absorbPointsCosted proof.hPieces, ([.challenge], 2),
      proofEvaluationBlocksCosted proof, ([.challenge, .challenge], 3),
      ([.point proof.multiopenQPrime.1], proof.multiopenQPrime.2 + 2), ([.challenge], 2),
      absorbScalarsCosted proof.multiopenU, ([.challenge], 2),
      ([.point proof.ipaS.1], proof.ipaS.2 + 2), ([.challenge, .challenge], 3)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil] at hcost
  change (preIpaTranscriptCosted proof).2 = _ + (preIpaTranscriptCosted proof).1.length + _ + _ at hcost
  conv at ha =>
    rhs
    simp only [plonkProofShape, FixtureMax.shape]
  conv at hl =>
    rhs
    simp only [plonkProofShape, FixtureMax.shape]
  conv at hp =>
    rhs
    simp only [plonkProofShape, FixtureMax.shape]
  conv at ht =>
    rhs
    simp only [plonkProofShape, FixtureMax.shape]
  conv at hh =>
    rhs
    simp only [plonkProofShape, FixtureMax.shape]
  conv at hu =>
    rhs
    simp only [plonkProofShape, FixtureMax.shape]
  nlinarith only [ha, hl, hp, ht, hh, he, hu, hr, hq, hs, hsize, hcost]

/-- The IPA block charges both complete point readers and every round marker. -/
theorem ipaRoundBlocksCosted_cost_le {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) (F × ℕ) (G × ℕ)) (access : ℕ)
    (hread : ProofFieldReadBound proof access) :
    (ipaRoundBlocksCosted proof).2 ≤ k * (2 * access + 12) + k * k + 1 := by
  apply flattenFinCosted_cost_le _ (2 * access + 7) 3
  · intro round
    have h := hread.ipaRounds round
    dsimp only
    omega
  · intro round
    exact le_rfl

/-- Every original point, scalar, and marker is covered by the complete attempt bound. -/
theorem plonkAttemptTraceCosted_cost_le {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) (F × ℕ) (G × ℕ)) (access : ℕ)
    (hread : ProofFieldReadBound proof access) :
    (plonkAttemptTraceCosted proof).2 ≤
      8 * actions * actions + (72 * actions + 2 * k + 63) * access +
        1300 * actions + k * k + 15 * k + 1900 := by
  have hp := preIpaTranscriptCosted_cost_le proof access hread
  have hi := ipaRoundBlocksCosted_cost_le proof access hread
  have hc := hread.ipaC
  have hf := hread.ipaF
  have hsize := plonkAttemptTraceCosted_length_le proof
  have hcost := concatTranscriptBlocksCosted_cost (α := TranscriptElt F G)
    [preIpaTranscriptCosted proof, ipaRoundBlocksCosted proof,
      ([TranscriptElt.scalar proof.ipaC.1, .scalar proof.ipaF.1], proof.ipaC.2 + proof.ipaF.2 + 5)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil] at hcost
  change (plonkAttemptTraceCosted proof).2 = _ + (plonkAttemptTraceCosted proof).1.length + _ + _ at hcost
  nlinarith only [hp, hi, hc, hf, hsize, hcost]

/-- Eleven IPA rounds give a fixed polynomial envelope in Action count and producer price. -/
theorem plonkAttemptTraceCosted_eleven_cost_le {actions : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions 11) (F × ℕ) (G × ℕ)) (access : ℕ)
    (hread : ProofFieldReadBound proof access) :
    (plonkAttemptTraceCosted proof).2 ≤
      8 * actions * actions + (72 * actions + 85) * access + 1300 * actions + 2200 := by
  have h := plonkAttemptTraceCosted_cost_le proof access hread
  nlinarith only [h]

end Zcash.Snark.ZeroKnowledge
