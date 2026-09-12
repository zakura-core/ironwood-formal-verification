import Zcash.Snark.ZeroKnowledge.ActionDerivedKey
import Zcash.Snark.ZeroKnowledge.PlonkOriginalRows

/-!
# Original row relations through the actual reference-key shape
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Snark Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS)

/-- Transporting a key's shape preserves arbitrary gate and paired lookup relations. -/
theorem verifyingKey_cast_constraintRelations {G : Type} {source target : CircuitShape}
    (hshape : source = target) (key : VerifyingKey source Fp G)
    (gateRelation : List (Expr Fp) → Prop)
    (lookupRelation : List (Expr Fp) → List (Expr Fp) → Prop)
    (hgates : gateRelation key.gates)
    (hlookups : ∀ lookup, lookupRelation (key.lookupInputExprs lookup) (key.lookupTableExprs lookup)) :
    gateRelation (hshape ▸ key).gates ∧
      ∀ lookup, lookupRelation ((hshape ▸ key).lookupInputExprs lookup) ((hshape ▸ key).lookupTableExprs lookup) := by
  cases hshape
  exact ⟨hgates, hlookups⟩

/-- The reference key retains all row equations of the actual compiled Action constraint system. -/
theorem actionReferenceKey_rows_of_verifierCS {G : Type} [AddCommGroup G] [Inhabited G] {actions : ℕ}
    (urs : URS G) (hk : urs.k = 11) (hpacked : actionCircuit.selectorMap.newFixedCols = 15)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (hgates : ∀ action : Fin actions, ∀ row : Fin 2048, ∀ expression ∈ actionCircuit.verifierCS.gates,
      plonkExpressionRowValue pub (plonkUnmaskedAdviceRows witness) action row expression = 0)
    (hlookups : ∀ action : Fin actions, ∀ lookup : Fin actionCircuit.lookupCount, ∀ row : Fin 2042,
      ∃ target : Fin 2042,
        (actionCircuit.verifierCS.lookupInputExprs lookup).map
          (plonkExpressionRowValue pub (plonkUnmaskedAdviceRows witness) action (row.castLE (by decide))) =
        (actionCircuit.verifierCS.lookupTableExprs lookup).map
          (plonkExpressionRowValue pub (plonkUnmaskedAdviceRows witness) action (target.castLE (by decide)))) :
    PlonkOriginalRowsValid (actionReferenceKey urs hk hpacked) pub witness := by
  have hcast := verifyingKey_cast_constraintRelations
    (actionCircuit_referenceShape actions urs.k hk hpacked) (actionCircuit.toVerifierKey urs)
    (fun gates => ∀ action : Fin actions, ∀ row : Fin 2048, ∀ expression ∈ gates,
      plonkExpressionRowValue pub (plonkUnmaskedAdviceRows witness) action row expression = 0)
    (fun inputs tables => ∀ action : Fin actions, ∀ row : Fin 2042, ∃ target : Fin 2042,
      inputs.map (plonkExpressionRowValue pub (plonkUnmaskedAdviceRows witness) action (row.castLE (by decide))) =
      tables.map (plonkExpressionRowValue pub (plonkUnmaskedAdviceRows witness) action (target.castLE (by decide))))
    hgates (fun lookup action row => hlookups action lookup row)
  exact ⟨hcast.1, fun action lookup row => hcast.2 lookup action row⟩

end Zcash.Snark.ZeroKnowledge
