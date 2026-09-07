import Zcash.Snark.ZeroKnowledge.TapeCausality
import Zcash.Snark.ZeroKnowledge.PlonkRowCausality

/-!
# Challenge dependencies on the actual batched prover tape

The actual decoder uses only the fixed column mask boundaries and batch order.
Replacing its retained-row callbacks changes no selected mask, coefficient, or
commitment blind. The earlier row-prefix lemmas therefore apply directly to the
private material computed from this tape, with no separate row-tape assumption.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- Every constructor choice gives the same declared boundaries in the same batches. -/
theorem plonkColumnBatches_shape {actions : ℕ}
    (left right : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp)) :
    (plonkColumnBatches left).map (List.map ColumnStep.firstMasked) =
      (plonkColumnBatches right).map (List.map ColumnStep.firstMasked) := by
  simp only [plonkColumnBatches, List.map_map, Function.comp_def]

/-- The actual pre-IPA decoder reads the same masks and private coins for any retained-row callbacks. -/
theorem plonkPreIpaCoinsEquiv_constructor_irrel {actions : ℕ}
    (left right : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (tape : Fin (batchedColumnSampleCount (plonkColumnBatches left) + 12) → Fp)
    (tape' : Fin (batchedColumnSampleCount (plonkColumnBatches right) + 12) → Fp)
    (htape : TapeAgrees tape tape') :
    TapeAgrees (plonkPreIpaCoinsEquiv left tape).1 (plonkPreIpaCoinsEquiv right tape').1 ∧
      (plonkPreIpaCoinsEquiv left tape).2 = (plonkPreIpaCoinsEquiv right tape').2 := by
  have h := batchedPreIpaCoins_shape_congr _ _ (plonkColumnBatches_shape left right) tape tape' htape
  refine ⟨?_, ?_⟩
  · intro i j hij
    exact h.1 _ _ hij
  · apply Prod.ext
    · exact h.2.1
    · funext i
      exact h.2.2 _ _ rfl

/-- Linear coefficients and all commitment blinds ignore retained-row callbacks and history. -/
theorem plonkMaterialFromTape_coins_congr {actions : ℕ}
    (left right : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history history' : ColumnHistory 2048)
    (tape : Fin (batchedColumnSampleCount (plonkColumnBatches left) + 12) → Fp)
    (tape' : Fin (batchedColumnSampleCount (plonkColumnBatches right) + 12) → Fp)
    (htape : TapeAgrees tape tape') :
    (plonkMaterialFromTape left history tape).2 = (plonkMaterialFromTape right history' tape').2 :=
  (plonkPreIpaCoinsEquiv_constructor_irrel left right tape tape' htape).2

/-- Matching constructors up to a cut suffice for equality of the actual decoded row prefix. -/
theorem plonkMaterialFromTape_rows_take {actions : ℕ} (cut : ℕ)
    (left right : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (tape : Fin (batchedColumnSampleCount (plonkColumnBatches left) + 12) → Fp)
    (tape' : Fin (batchedColumnSampleCount (plonkColumnBatches right) + 12) → Fp)
    (hsteps : (plonkColumnSteps left).take cut = (plonkColumnSteps right).take cut)
    (htape : TapeAgrees tape tape') :
    (plonkMaterialFromTape left history tape).1.take cut =
      (plonkMaterialFromTape right history tape').1.take cut := by
  apply columnRowsFromTape_take_congr
  · exact hsteps
  · exact (plonkPreIpaCoinsEquiv_constructor_irrel left right tape tape' htape).1

/-- Equal callbacks and corresponding input positions give the same complete private material. -/
theorem plonkMaterialFromTape_congr {actions : ℕ}
    (left right : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (tape : Fin (batchedColumnSampleCount (plonkColumnBatches left) + 12) → Fp)
    (tape' : Fin (batchedColumnSampleCount (plonkColumnBatches right) + 12) → Fp)
    (hconstruct : left = right) (htape : TapeAgrees tape tape') :
    plonkMaterialFromTape left history tape = plonkMaterialFromTape right history tape' := by
  subst right
  rw [htape.eq]

/-- The actual batched advice-row prefix is fixed before any verifier challenge is received. -/
theorem plonkMaterialFromTape_before_theta {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (left right : Challenges k Fp)
    (tape : Fin (batchedColumnSampleCount
      (plonkColumnBatches (plonkTotalColumnConstructor vk pub witness left)) + 12) → Fp)
    (tape' : Fin (batchedColumnSampleCount
      (plonkColumnBatches (plonkTotalColumnConstructor vk pub witness right)) + 12) → Fp)
    (htape : TapeAgrees tape tape') :
    (plonkMaterialFromTape (plonkTotalColumnConstructor vk pub witness left) [] tape).1.take (10 * actions) =
      (plonkMaterialFromTape (plonkTotalColumnConstructor vk pub witness right) [] tape').1.take (10 * actions) :=
  plonkMaterialFromTape_rows_take _ _ _ [] tape tape'
    (plonkColumnSteps_take_before_theta vk pub witness left right) htape

/-- Advice and permuted lookup rows on the actual tape use only the already received `theta`. -/
theorem plonkMaterialFromTape_before_products {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (left right : Challenges k Fp)
    (tape : Fin (batchedColumnSampleCount
      (plonkColumnBatches (plonkTotalColumnConstructor vk pub witness left)) + 12) → Fp)
    (tape' : Fin (batchedColumnSampleCount
      (plonkColumnBatches (plonkTotalColumnConstructor vk pub witness right)) + 12) → Fp)
    (htheta : left.theta = right.theta) (htape : TapeAgrees tape tape') :
    (plonkMaterialFromTape (plonkTotalColumnConstructor vk pub witness left) [] tape).1.take (16 * actions) =
      (plonkMaterialFromTape (plonkTotalColumnConstructor vk pub witness right) [] tape').1.take (16 * actions) :=
  plonkMaterialFromTape_rows_take _ _ _ [] tape tape'
    (plonkColumnSteps_take_challenges vk pub witness left right htheta) htape

/-- The whole actual private material uses no challenges after `theta,beta,gamma`. -/
theorem plonkMaterialFromTape_challenges {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (witness : Fin actions → Fin 10 → Fin 2048 → Fp) (left right : Challenges k Fp)
    (tape : Fin (batchedColumnSampleCount
      (plonkColumnBatches (plonkTotalColumnConstructor vk pub witness left)) + 12) → Fp)
    (tape' : Fin (batchedColumnSampleCount
      (plonkColumnBatches (plonkTotalColumnConstructor vk pub witness right)) + 12) → Fp)
    (htheta : left.theta = right.theta) (hbeta : left.beta = right.beta) (hgamma : left.gamma = right.gamma)
    (htape : TapeAgrees tape tape') :
    plonkMaterialFromTape (plonkTotalColumnConstructor vk pub witness left) [] tape =
      plonkMaterialFromTape (plonkTotalColumnConstructor vk pub witness right) [] tape' :=
  plonkMaterialFromTape_congr _ _ [] tape tape'
    (plonkTotalColumnConstructor_challenges vk pub witness left right htheta hbeta hgamma) htape

/-- Separating the IPA suffix from a complete prover tape uses no retained-row computation. -/
theorem plonkJointTape_split_congr {actions k : ℕ}
    (left right : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (tape : Fin (plonkJointSampleCount left k) → Fp)
    (tape' : Fin (plonkJointSampleCount right k) → Fp) (htape : TapeAgrees tape tape') :
    TapeAgrees
        (splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches left) + 12) (ipaSampleCount k) Fp tape).1
        (splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches right) + 12) (ipaSampleCount k) Fp tape').1 ∧
      (splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches left) + 12) (ipaSampleCount k) Fp tape).2 =
        (splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches right) + 12) (ipaSampleCount k) Fp tape').2 := by
  constructor
  · intro i j hij
    exact htape _ _ hij
  · funext i
    apply htape
    change (batchedColumnSampleCount (plonkColumnBatches left) + 12) + i.val =
      (batchedColumnSampleCount (plonkColumnBatches right) + 12) + i.val
    rw [plonkColumnBatches_sample_count, plonkColumnBatches_sample_count]

/-- The exact private material computed inside `plonkJointViewFromTape`, before the IPA suffix is used. -/
def plonkJointMaterialFromTape {actions k : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (tape : Fin (plonkJointSampleCount construct k) → Fp) :
    PlonkPrivateMaterial actions :=
  plonkMaterialFromTape construct history
    (splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches construct) + 12) (ipaSampleCount k) Fp tape).1

/-- On a complete prover tape, the coefficients and commitment blinds ignore all retained-row callbacks. -/
theorem plonkJointMaterialFromTape_coins_congr {actions k : ℕ}
    (left right : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history history' : ColumnHistory 2048)
    (tape : Fin (plonkJointSampleCount left k) → Fp)
    (tape' : Fin (plonkJointSampleCount right k) → Fp) (htape : TapeAgrees tape tape') :
    (plonkJointMaterialFromTape left history tape).2 = (plonkJointMaterialFromTape right history' tape').2 :=
  plonkMaterialFromTape_coins_congr left right history history' _ _
    (plonkJointTape_split_congr left right tape tape' htape).1

/-- Earlier construction steps determine the row prefix on the complete prover tape. -/
theorem plonkJointMaterialFromTape_rows_take {actions k : ℕ} (cut : ℕ)
    (left right : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (tape : Fin (plonkJointSampleCount left k) → Fp)
    (tape' : Fin (plonkJointSampleCount right k) → Fp)
    (hsteps : (plonkColumnSteps left).take cut = (plonkColumnSteps right).take cut)
    (htape : TapeAgrees tape tape') :
    (plonkJointMaterialFromTape left history tape).1.take cut =
      (plonkJointMaterialFromTape right history tape').1.take cut :=
  plonkMaterialFromTape_rows_take cut left right history _ _ hsteps
    (plonkJointTape_split_congr left right tape tape' htape).1

/-- Matching callbacks give equal complete private materials on the complete prover tape. -/
theorem plonkJointMaterialFromTape_congr {actions k : ℕ}
    (left right : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048)
    (tape : Fin (plonkJointSampleCount left k) → Fp)
    (tape' : Fin (plonkJointSampleCount right k) → Fp)
    (hconstruct : left = right) (htape : TapeAgrees tape tape') :
    plonkJointMaterialFromTape left history tape = plonkJointMaterialFromTape right history tape' :=
  plonkMaterialFromTape_congr left right history _ _ hconstruct
    (plonkJointTape_split_congr left right tape tape' htape).1

end Zcash.Snark.ZeroKnowledge
