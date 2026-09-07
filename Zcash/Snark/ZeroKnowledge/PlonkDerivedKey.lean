import Zcash.Snark.ZeroKnowledge.PlonkKeygenCommitments
import Zcash.Snark.ZeroKnowledge.PlonkQueryLayout
import Zcash.Snark.ZeroKnowledge.PlonkVerifierOpening

/-!
# Public commitment agreement for a compiler-derived verifying key

The key is the existing `TopLevelCircuit.toVerifierKey`, transported only across
an equality of circuit dimensions. Its public commitments agree with the reference
compiler polynomials. The query layout supplies the required fixed-column coverage;
the shape supplies all fifteen sigma columns. Commitment agreement is a conclusion,
not an extra premise about those group points.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS omegaOf)
open Halo2

variable {G : Type}
variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- Reference public data obtained entirely from the compiler and its public-input layout. -/
def plonkCompilerPublicPolynomials {actions : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput) (inputs : Fin actions → PublicInput Fp) :
    PlonkPublicPolynomials actions :=
  plonkKeygenPublicPolynomials top
    (fun a row => (top.publicInputRows (inputs a) ⟨0⟩).getD row.val 0)
    (plonkKeygenSigmaRows top)

private theorem castKey_fixedLayout {s t : CircuitShape} (h : s = t)
    (vk : VerifyingKey s Fp G) : (h ▸ vk).fixedQueryLayout = vk.fixedQueryLayout := by
  cases h
  rfl

private theorem castKey_fixedCommitment {s t : CircuitShape} (h : s = t)
    (vk : VerifyingKey s Fp G) (column : ℕ) :
    (h ▸ vk).fixedCommitment column = vk.fixedCommitment column := by
  cases h
  rfl

private theorem castKey_sigmaCommitment {s t : CircuitShape} (h : s = t)
    (vk : VerifyingKey s Fp G) (column : Fin t.numPermutationColumns) :
    (h ▸ vk).permutationCommonCommitment column =
      vk.permutationCommonCommitment
        (column.cast (congrArg CircuitShape.numPermutationColumns h).symm) := by
  cases h
  rfl

private theorem castKey_n {s t : CircuitShape} (h : s = t) (vk : VerifyingKey s Fp G) :
    (h ▸ vk).n = vk.n := by
  cases h
  rfl

private theorem castKey_omega {s t : CircuitShape} (h : s = t) (vk : VerifyingKey s Fp G) :
    (h ▸ vk).omega = vk.omega := by
  cases h
  rfl

/-- The reference fixed-query layout guarantees that the compiler really has all twenty-nine columns. -/
theorem plonkCompilerFixedColumnCoverage (top : TopLevelCircuit Fp Config PublicInput)
    (hlayout : top.fixedQueryLayout =
      List.ofFn (fun j : Fin 29 => ((plonkFixedQueryOrder j).val, (0 : ℤ)))) :
    29 ≤ top.fixedColumnCount := by
  have hlast : (28, (0 : ℤ)) ∈ top.fixedQueryLayout := by
    rw [hlayout, List.mem_ofFn]
    exact ⟨28, rfl⟩
  exact List.forall_iff_forall_mem.mp top.fixedQueryLayout_columns_lt (28, 0) hlast

-- Compare named compiler projections without reducing the full row tables.
attribute [local irreducible] rowPolynomial Zcash.Arithmetic.omegaOf polynomialCommitment

/-- Actual compiler key generation discharges all three public commitment agreement conditions. -/
theorem plonkCompilerPublicCommitmentsMatch [AddCommGroup G] [Module Fp G] [Inhabited G]
    {actions : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput) (urs : URS G) (hurs : urs.k = 11)
    (hshape : top.shape = (plonkProofShape actions urs.k).toCircuitShape)
    (hlayout : PlonkQueryLayout (hshape ▸ top.toVerifierKey urs))
    (inputs : Fin actions → PublicInput Fp) :
    PlonkPublicCommitmentsMatch urs (hshape ▸ top.toVerifierKey urs)
      (plonkCompilerPublicPolynomials top inputs) (top.instanceCommitment urs inputs) := by
  have htop : top.domainExponent = 11 :=
    (show top.domainExponent = urs.k from congrArg CircuitShape.k hshape).trans hurs
  have hperm : top.permutationColumnCount = 15 :=
    congrArg CircuitShape.numPermutationColumns hshape
  have hfixedLayout := hlayout.fixed
  rw [castKey_fixedLayout, TopLevelCircuit.toVerifierKey_fixedQueryLayout] at hfixedLayout
  have hcolumns := plonkCompilerFixedColumnCoverage top hfixedLayout
  constructor
  · intro a
    exact plonkKeygenInstanceCommitment top urs htop hurs inputs a
  · intro column
    rw [castKey_fixedCommitment, TopLevelCircuit.toVerifierKey_fixedCommitment]
    exact plonkKeygenFixedCommitment top urs htop hurs column (column.isLt.trans_le hcolumns)
  · intro column
    rw [castKey_sigmaCommitment, TopLevelCircuit.toVerifierKey_permutationCommonCommitment]
    exact plonkKeygenSigmaCommitment top urs htop hurs column (by rw [hperm]; exact column.isLt)

/-- A compiler key with the reference shape and eleven IPA rounds has the reference domain and root. -/
theorem plonkCompilerKey_domain [AddCommGroup G] [Inhabited G] {actions : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput) (urs : URS G) (hurs : urs.k = 11)
    (hshape : top.shape = (plonkProofShape actions urs.k).toCircuitShape) :
    (hshape ▸ top.toVerifierKey urs).n = 2048 ∧
      (hshape ▸ top.toVerifierKey urs).omega = omegaOf 11 := by
  have htop : top.domainExponent = 11 :=
    (show top.domainExponent = urs.k from congrArg CircuitShape.k hshape).trans hurs
  rw [castKey_n, castKey_omega, TopLevelCircuit.toVerifierKey_n,
    TopLevelCircuit.toVerifierKey_omega, TopLevelCircuit.n, TopLevelCircuit.omega, htop]
  exact ⟨rfl, rfl⟩

/-- The compiler-derived key's actual opening equals the reference without a commitment-agreement premise. -/
theorem plonkCompilerOpening_eq_public [AddCommGroup G] [Module Fp G] [Inhabited G] [DecidableEq G]
    {actions : ℕ} (top : TopLevelCircuit Fp Config PublicInput) (urs : URS G) (hurs : urs.k = 11)
    (hshape : top.shape = (plonkProofShape actions urs.k).toCircuitShape)
    (hlayout : PlonkQueryLayout (hshape ▸ top.toVerifierKey urs))
    (inputs : Fin actions → PublicInput Fp) (ch : Challenges urs.k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript urs.k Fp G)
    (hpositive : 0 < actions)
    (hpoints : Function.Injective (plonkQueryPoint (omegaOf 11) ch.x)) :
    let vk := hshape ▸ top.toVerifierKey urs
    let pub := plonkCompilerPublicPolynomials top inputs
    let actual := plonkVerifierOpening urs vk pub (top.instanceCommitment urs inputs) ch view
    let reference := plonkPublicOpening urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3
      (plonkVerifierHx vk pub ch (privateColumnView view.1.2.1)) view.1
    (actual.1.eval urs, actual.2) = (reference.1.eval urs, reference.2) := by
  have hdomain := plonkCompilerKey_domain top urs hurs hshape
  exact plonkVerifierOpening_eq_public urs _ hlayout _ _ ch view hpositive
    (by rw [hdomain.2]; exact hpoints)
    (plonkCompilerPublicCommitmentsMatch top urs hurs hshape hlayout inputs)
    hdomain.1 hdomain.2

end Zcash.Snark.ZeroKnowledge
