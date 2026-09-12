import Zcash.Snark.ZeroKnowledge.PlonkClaimQueriesCost
import Zcash.Snark.ZeroKnowledge.PlonkClaimInputBounds
import Zcash.Snark.ZeroKnowledge.ConstraintCollectionCost
import Zcash.Snark.ZeroKnowledge.PlonkPublicRows

/-!
# Complete constraint computation from the actual PLONK claims

Public query reads include polynomial preparation. Private query reads follow
the original column and observation schedules. Permutation and lookup inputs
are constructed and paid for before the complete constraint list is evaluated.
The key expression and layout preparation costs remain explicit inputs.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp omegaOf)

/-- Construct every query and argument input, then evaluate the complete ordered constraint list. -/
def plonkClaimConstraintsCosted (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions : ℕ} (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (gates : List (Expr Fp) × ℕ)
    (layout : List (List (ColumnRef × ℕ)) × ℕ) (inputs tables : Fin 3 → List (Expr Fp) × ℕ)
    (beta gamma x delta theta : Fp × ℕ) (stride : ℕ) (l0 lLast lBlind : Fp × ℕ) : List Fp × ℕ :=
  let fixedQueries := plonkFixedQueryCosted costs omegaAccess fixed x
  let adviceQueries := plonkAdviceQueryCosted (actions := actions) equal read views
  let instanceQueries := fun action =>
    publicRowQueryCosted costs omegaAccess (fun _ : Fin 1 => instances action) x
  let sigmaQueries := publicRowQueryCosted costs omegaAccess sigma x
  let sets := plonkPermutationSetsCosted (actions := actions) equal read views
  let chunks := fun action => permutationQueryChunksCosted (instanceQueries action)
    (adviceQueries action) fixedQueries sigmaQueries (sets action) layout
  let lookups := fun action : Fin actions => plonkLookupInputsCosted equal read views action inputs tables
  let result := allConstraintsCosted costs node fixedQueries adviceQueries instanceQueries gates.1
    sets chunks lookups beta gamma x delta theta stride l0 lLast lBlind
  (result.1, gates.2 + result.2 + 1)

set_option maxRecDepth 5000 in
/-- Erasure is the verifier's full constraint list at the original claim proof. -/
theorem plonkClaimConstraintsCosted_result (costs : FieldOperationCosts) (node equal read omegaAccess : ℕ)
    {actions k : ℕ} {G : Type*} [Zero G] (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (instances : Fin actions → Fin 2048 → Fp × ℕ)
    (fixed : Fin 29 → Fin 2048 → Fp × ℕ) (sigma : Fin 15 → Fin 2048 → Fp × ℕ)
    (views : List (Fin 5 → Fp × ℕ)) (gateCost layoutCost : ℕ) (inputCost tableCost : Fin 3 → ℕ)
    (ch : Challenges k Fp) (betaCost gammaCost xCost deltaCost thetaCost : ℕ)
    (l0 lLast lBlind : Fp × ℕ) :
    (plonkClaimConstraintsCosted costs node equal read omegaAccess instances fixed sigma views
      (vk.gates, gateCost) (vk.permutationChunks, layoutCost)
      (fun index => (vk.lookupInputExprs index, inputCost index))
      (fun index => (vk.lookupTableExprs index, tableCost index))
      (ch.beta, betaCost) (ch.gamma, gammaCost) (ch.x, xCost) (vk.delta, deltaCost)
      (ch.theta, thetaCost) vk.chunkLen l0 lLast lBlind).1 =
      allExpressions vk
        (plonkClaimProof
          (fun action => (rowPolynomial (omegaOf 11) (fun row => (instances action row).1)).eval ch.x)
          (fun column => (rowPolynomial (omegaOf 11) (fun row => (fixed column row).1)).eval ch.x)
          (fun column => (rowPolynomial (omegaOf 11) (fun row => (sigma column row).1)).eval ch.x)
          (fun id point => privateColumnView (views.map (fun column i => (column i).1)) id point.castSucc))
        ch l0.1 lLast.1 lBlind.1 := by
  let instanceValues := fun action =>
    (rowPolynomial (omegaOf 11) (fun row => (instances action row).1)).eval ch.x
  let fixedValues := fun column =>
    (rowPolynomial (omegaOf 11) (fun row => (fixed column row).1)).eval ch.x
  let sigmaValues := fun column =>
    (rowPolynomial (omegaOf 11) (fun row => (sigma column row).1)).eval ch.x
  let ps : ProofString (plonkProofShape actions k) Fp G :=
    plonkClaimProof instanceValues fixedValues sigmaValues
      (fun id point => privateColumnView (views.map (fun column i => (column i).1)) id point.castSucc)
  let fixedQueries := plonkFixedQueryCosted costs omegaAccess fixed (ch.x, xCost)
  let adviceQueries := plonkAdviceQueryCosted (actions := actions) equal read views
  let instanceQueries := fun action =>
    publicRowQueryCosted costs omegaAccess (fun _ : Fin 1 => instances action) (ch.x, xCost)
  let sigmaQueries := publicRowQueryCosted costs omegaAccess sigma (ch.x, xCost)
  let sets := plonkPermutationSetsCosted (actions := actions) equal read views
  let chunks := fun action => permutationQueryChunksCosted (instanceQueries action)
    (adviceQueries action) fixedQueries sigmaQueries (sets action) (vk.permutationChunks, layoutCost)
  let lookups := fun action : Fin actions => plonkLookupInputsCosted equal read views action
    (fun index => (vk.lookupInputExprs index, inputCost index))
    (fun index => (vk.lookupTableExprs index, tableCost index))
  have hf (index : ℕ) : (fixedQueries index).1 = finFn ps.fixedEvals index := by
    rw [plonkFixedQueryCosted_result]
    dsimp only [ps, plonkClaimProof, plonkProofString, fixedValues]
    rfl
  have ha (action : Fin actions) (index : ℕ) : (adviceQueries action index).1 =
      finFn (ps.adviceEvals action) index := by
    exact plonkAdviceQueryCosted_result (k := k) (G := G) equal read views action index
      instanceValues fixedValues sigmaValues
  have hi (action : Fin actions) (index : ℕ) : (instanceQueries action index).1 =
      finFn (ps.instanceEvals action) index := by
    rw [publicRowQueryCosted_result]
    dsimp only [ps, plonkClaimProof, plonkProofString, instanceValues]
    rfl
  have hs (index : ℕ) : (sigmaQueries index).1 = finFn ps.permutationCommonEvals index := by
    rw [publicRowQueryCosted_result]
    dsimp only [ps, plonkClaimProof, plonkProofString, sigmaValues]
    rfl
  have hsets (action : Fin actions) : (sets action).1.map (PermSetEval.map Prod.fst) =
      subProofPermSets ps action :=
    plonkPermutationSetsCosted_result (k := k) (G := G) equal read views action
      instanceValues fixedValues sigmaValues
  have hchunks (action : Fin actions) : (chunks action).1.map
      (fun chunk => (chunk.1.map Prod.fst, chunk.2.map Prod.fst)) = subProofPermChunks vk ps action := by
    change (permutationQueryChunksCosted (instanceQueries action) (adviceQueries action)
      fixedQueries sigmaQueries (sets action) (vk.permutationChunks, layoutCost)).1.map _ = _
    rw [permutationQueryChunksCosted_result, hsets]
    simp only [hi, ha, hf, hs, subProofPermChunks]
  have hlookups (action : Fin actions) : (lookups action).1.map
      (fun lookup => (lookup.1.map Prod.fst, lookup.2.1, lookup.2.2)) = subProofLookups vk ps action := by
    exact plonkLookupInputsCosted_result (k := k) (G := G) equal read views action
      (fun index => (vk.lookupInputExprs index, inputCost index))
      (fun index => (vk.lookupTableExprs index, tableCost index)) instanceValues fixedValues sigmaValues
  change (allConstraintsCosted costs node fixedQueries adviceQueries instanceQueries vk.gates
    sets chunks lookups (ch.beta, betaCost) (ch.gamma, gammaCost) (ch.x, xCost) (vk.delta, deltaCost)
    (ch.theta, thetaCost) vk.chunkLen l0 lLast lBlind).1 = allExpressions vk ps ch l0.1 lLast.1 lBlind.1
  rw [allConstraintsCosted_result, allExpressions_eq]
  simp only [hf, ha, hi, hsets, hchunks, hlookups]
  rfl


end Zcash.Snark.ZeroKnowledge
