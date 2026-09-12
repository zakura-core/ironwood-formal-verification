import Zcash.Snark.ZeroKnowledge.ProofRecordProducerCost
import Zcash.Snark.ZeroKnowledge.PlonkClaimInputsCost
import Zcash.Snark.ZeroKnowledge.CommitmentEntryCost

/-!
# Complete producer prices on the original proof-field routing

Public scalar producers, materialized private observations, commitment readers,
and IPA readers feed the actual twenty-field proof type. Every private route and
query-table lookup is counted. Permutation and lookup fields retain their entire
record preparation cost, including the optional permutation branch.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Read a fixed scalar through the actual query-order table. -/
def fixedClaimReaderCosted (fixed : Fin 29 → Fp × ℕ) (query : Fin 29) : Fp × ℕ :=
  let index := fixedQueryOrderCosted query
  let value := fixed index.1
  (value.1, index.2 + value.2 + 1)

/-- Fixed-scalar routing preserves the canonical query order. -/
theorem fixedClaimReaderCosted_result (fixed : Fin 29 → Fp × ℕ) (query : Fin 29) :
    (fixedClaimReaderCosted fixed query).1 = (fixed (plonkFixedQueryOrder query)).1 := by
  simp only [fixedClaimReaderCosted, fixedQueryOrderCosted_result]

/-- The fixed claim pays for both the query table and its complete scalar producer. -/
theorem fixedClaimReaderCosted_cost_le (fixed : Fin 29 → Fp × ℕ) (query : Fin 29)
    (access : ℕ) (hread : ∀ column, (fixed column).2 ≤ access) :
    (fixedClaimReaderCosted fixed query).2 ≤ access + 120 := by
  have hquery := fixedQueryOrderCosted_cost_le query
  have hvalue := hread (fixedQueryOrderCosted query).1
  dsimp only [fixedClaimReaderCosted]
  omega

/-- Supply complete priced readers for every field in the original PLONK and IPA proof. -/
def plonkRoutedProofCosts (equal read : ℕ) {actions k : ℕ} {G : Type*}
    (instances : Fin actions → Fp × ℕ) (fixed : Fin 29 → Fp × ℕ) (sigma : Fin 15 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (points : Fin (22 * actions + 10) → G × ℕ)
    (rEval : Fp × ℕ) (groupValues : Fin 5 → Fp × ℕ)
    (tail : IpaTranscript k (Fp × ℕ) (G × ℕ)) :
    ProofString (plonkProofShape actions k) (Fp × ℕ) (G × ℕ) where
  adviceCommitments := fun action column => plonkColumnEntryCosted equal points (.advice action column)
  lookupPermutedInput := fun action lookup => plonkColumnEntryCosted equal points (.lookupInput action lookup)
  lookupPermutedTable := fun action lookup => plonkColumnEntryCosted equal points (.lookupTable action lookup)
  permutationProduct := fun action set => plonkColumnEntryCosted equal points (.permutationProduct action set)
  lookupProduct := fun action lookup => plonkColumnEntryCosted equal points (.lookupProduct action lookup)
  vanishingRandom := plonkLinearEntryCosted points
  hPieces := plonkPieceEntryCosted points
  instanceEvals := fun action _ => instances action
  adviceEvals := plonkAdviceClaimCosted equal read views
  fixedEvals := fixedClaimReaderCosted fixed
  vanishingRandomEval := rEval
  permutationCommonEvals := sigma
  permutationSetEvals := fun action set =>
    payPermSetProducer (plonkPermutationSetCosted equal read views action set)
  lookupEvals := fun action lookup =>
    payLookupProducer (plonkLookupEvalCosted equal read views action lookup)
  multiopenQPrime := plonkQuotientPrimeEntryCosted points
  multiopenU := groupValues
  ipaS := tail.maskCommitment
  ipaRounds := tail.messages
  ipaC := tail.scalar
  ipaF := tail.blind

/-- Erasing prices recovers all original fields, routes, and optional claims exactly. -/
theorem plonkRoutedProofCosts_result (equal read : ℕ) {actions k : ℕ} {G : Type*}
    (instances : Fin actions → Fp × ℕ) (fixed : Fin 29 → Fp × ℕ) (sigma : Fin 15 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (points : Fin (22 * actions + 10) → G × ℕ)
    (rEval : Fp × ℕ) (groupValues : Fin 5 → Fp × ℕ)
    (tail : IpaTranscript k (Fp × ℕ) (G × ℕ)) :
    eraseProofCosts (plonkRoutedProofCosts equal read instances fixed sigma views points rEval groupValues tail) =
      plonkProofString (fun action => (instances action).1) (fun column => (fixed column).1)
        (fun column => (sigma column).1)
        (fun id point => privateColumnView (views.map (fun column index => (column index).1)) id point.castSucc)
        (fun index => (points index).1) rEval.1 (fun group => (groupValues group).1)
        { maskCommitment := tail.maskCommitment.1,
          messages := fun round => ((tail.messages round).1.1, (tail.messages round).2.1),
          scalar := tail.scalar.1, blind := tail.blind.1 } := by
  have hperm (action : Fin actions) (set : Fin 3) :=
    plonkPermutationSetCosted_result (k := k) (G := Fp) equal read views action set
      (fun a => (instances a).1) (fun column => (fixed column).1) (fun column => (sigma column).1)
  have hlookup (action : Fin actions) (lookup : Fin 3) :=
    plonkLookupEvalCosted_result (k := k) (G := Fp) equal read views action lookup
      (fun a => (instances a).1) (fun column => (fixed column).1) (fun column => (sigma column).1)
  have hadvice (action : Fin actions) (query : Fin 25) :=
    plonkAdviceClaimCosted_result (k := k) (G := Fp) equal read views action query
      (fun a => (instances a).1) (fun column => (fixed column).1) (fun column => (sigma column).1)
  simp only [plonkClaimProof, plonkProofString] at hperm hlookup hadvice
  simp only [eraseProofCosts, plonkRoutedProofCosts, plonkColumnEntryCosted_result,
    plonkLinearEntryCosted_result, plonkPieceEntryCosted_result, fixedClaimReaderCosted_result,
    plonkQuotientPrimeEntryCosted_result, payPermSetProducer_result, payLookupProducer_result,
    plonkProofString]
  congr 1
  · exact funext fun action => funext fun query => hadvice action query
  · exact funext fun action => funext fun set => hperm action set
  · exact funext fun action => funext fun lookup => hlookup action lookup

end Zcash.Snark.ZeroKnowledge
