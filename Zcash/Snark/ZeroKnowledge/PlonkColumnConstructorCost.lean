import Zcash.Snark.ZeroKnowledge.PlonkLookupSortCost
import Zcash.Snark.ZeroKnowledge.PlonkLookupProductCostBound
import Zcash.Snark.ZeroKnowledge.PlonkPermutationProductCostBound
import Zcash.Snark.ZeroKnowledge.StoredPlonkKeyCost
import Zcash.Snark.ZeroKnowledge.PlonkConstruction

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark Zcash.Arithmetic

/-- Execute the original private-column dispatcher while retaining every future row-reader cost. -/
def plonkConstructColumnResultCosted (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions : ℕ} (stored : StoredPlonkKey)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (theta beta gamma : Fp × ℕ)
    (id : PrivateColumnId actions) (history : List (Fin 2048 → Fp × ℕ)) :
    Option (Fin 2048 → Fp × ℕ) × ℕ :=
  match id with
  | .advice a c => (some (witness a c), 1)
  | .lookupInput a l =>
      let reversed := reverseListCosted history
      let sorted := plonkLookupSortedRowsCosted costs node equal read omegaAccess canonicalRead compare
        instances fixed reversed.1 theta a (stored.lookupInputCosted read l) (stored.lookupTableCosted read l)
      (sorted.1.map (fun output row => getDListCosted read 0 output.1 row.val), reversed.2 + sorted.2 + 2)
  | .lookupTable a l =>
      let reversed := reverseListCosted history
      let sorted := plonkLookupSortedRowsCosted costs node equal read omegaAccess canonicalRead compare
        instances fixed reversed.1 theta a (stored.lookupInputCosted read l) (stored.lookupTableCosted read l)
      (sorted.1.map (fun output row => getDListCosted read 0 output.2 row.val), reversed.2 + sorted.2 + 2)
  | .permutationProduct a s =>
      let reversed := reverseListCosted history
      (some (plonkPermutationBaseRowsCosted costs equal read omegaAccess instances fixed sigma reversed.1
        beta gamma (stored.delta, read + 1) (stored.chunkLen, read + 1) (stored.layoutCosted read) a s),
        reversed.2 + 2)
  | .lookupProduct a l =>
      let reversed := reverseListCosted history
      (some (plonkLookupBaseRowsCosted costs node equal read omegaAccess instances fixed reversed.1 theta beta gamma
        a l (stored.lookupInputCosted read l) (stored.lookupTableCosted read l)), reversed.2 + 2)

/-- Erasure is the complete original partial constructor, with the original newest-first history. -/
theorem plonkConstructColumnResultCosted_result (costs : FieldOperationCosts)
    (node equal read omegaAccess canonicalRead compare : ℕ) {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp × ℕ) (ch : Challenges k Fp)
    (thetaRead betaRead gammaRead : ℕ) (id : PrivateColumnId actions)
    (history : List (Fin 2048 → Fp × ℕ)) :
    (plonkConstructColumnResultCosted costs node equal read omegaAccess canonicalRead compare
      (StoredPlonkKey.encode vk) instances fixed sigma witness (ch.theta, thetaRead) (ch.beta, betaRead)
      (ch.gamma, gammaRead) id history).1.map (fun column row => (column row).1) =
      plonkConstructColumnResult vk
        (plonkPublicPolynomialsFromRows (fun a r => (instances a r).1)
          (fun c r => (fixed c r).1) (fun c r => (sigma c r).1))
        (fun a c r => (witness a c r).1) ch id (history.map (fun column r => (column r).1)) := by
  have hi (l : Fin 3) : (StoredPlonkKey.encode vk).lookupInputCosted read l =
      (vk.lookupInputExprs l, ((StoredPlonkKey.encode vk).lookupInputCosted read l).2) :=
    Prod.ext (StoredPlonkKey.lookupInputCosted_encode_result vk read l) rfl
  have ht (l : Fin 3) : (StoredPlonkKey.encode vk).lookupTableCosted read l =
      (vk.lookupTableExprs l, ((StoredPlonkKey.encode vk).lookupTableCosted read l).2) :=
    Prod.ext (StoredPlonkKey.lookupTableCosted_encode_result vk read l) rfl
  cases id with
  | advice a c => rfl
  | lookupInput a l =>
      simp only [plonkConstructColumnResultCosted, plonkConstructColumnResult, reverseListCosted_result,
        Option.map_map, Function.comp_def, getDListCosted_result]
      rw [hi l, ht l]
      simp only [plonkLookupSortedRowsCosted_result costs node equal read omegaAccess canonicalRead compare
        vk instances fixed (fun c r => (sigma c r).1), List.map_reverse]
  | lookupTable a l =>
      simp only [plonkConstructColumnResultCosted, plonkConstructColumnResult, reverseListCosted_result,
        Option.map_map, Function.comp_def, getDListCosted_result]
      rw [hi l, ht l]
      simp only [plonkLookupSortedRowsCosted_result costs node equal read omegaAccess canonicalRead compare
        vk instances fixed (fun c r => (sigma c r).1), List.map_reverse]
  | permutationProduct a s =>
      simp only [plonkConstructColumnResultCosted, plonkConstructColumnResult, reverseListCosted_result,
        Option.map_some, StoredPlonkKey.layoutCosted, StoredPlonkKey.encode,
        plonkPermutationBaseRowsCosted_result costs equal read omegaAccess vk instances fixed sigma, List.map_reverse]
  | lookupProduct a l =>
      simp only [plonkConstructColumnResultCosted, plonkConstructColumnResult, reverseListCosted_result, Option.map_some]
      rw [hi l, ht l]
      simp only [plonkLookupBaseRowsCosted_result costs node equal read omegaAccess
        vk instances fixed (fun c r => (sigma c r).1), List.map_reverse]

end Zcash.Snark.ZeroKnowledge
