import Zcash.Snark.ZeroKnowledge.PlonkKeygenFixed
import Zcash.Snark.ZeroKnowledge.PlonkKeygenSigmaRows
import Zcash.Snark.ZeroKnowledge.PlonkCommitmentRouting
import Zcash.Circuits.Integration.PermutationColumns
import Zcash.Circuits.Integration.TopLevelInstanceCommitment

/-!
# Compiler commitments to the reference public polynomials

The existing key-generation correctness lemmas relate the compiler's Lagrange
commitments to its dense rows. These connectors identify the resulting monomial
commitments with the same row interpolants used by the reference prover, including
the default public blind of one. No commitment-binding assumption is needed.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS omegaOf)
open Halo2

variable {G : Type} [AddCommGroup G] [Module Fp G] [Inhabited G]
variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

-- Domain rewrites compare interpolants structurally, without evaluating their 2048 terms.
attribute [local irreducible] rowPolynomial omegaOf

omit [Inhabited G] in
/-- The Lagrange committer and reference polynomial committer agree on the same interpolant. -/
theorem lagrangeCommitInstance_eq_polynomialCommitment (urs : URS G) (omega : Fp)
    (key : LagrangeCommitmentKey urs omega) (rows : List Fp) (blind : Fp) :
    key.commitInstance rows blind =
      polynomialCommitment urs.g urs.w (instanceRowPolynomial (2 ^ urs.k) omega rows) blind := by
  rw [LagrangeCommitmentKey.commitInstance_eq]
  rfl

/-- The actual compiler's fixed commitment is the reference fixed-row polynomial commitment. -/
theorem plonkKeygenFixedCommitment (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G) (htop : top.domainExponent = 11) (hurs : urs.k = 11)
    (column : Fin 29) (hcolumn : column.val < top.fixedColumnCount) :
    (top.fixedCommitments urs).getD column.val 0 =
      polynomialCommitment urs.g urs.w
        (rowPolynomial (omegaOf 11) (plonkKeygenFixedRows top column)) 1 := by
  have hcoherent := TopLevelFixedCoherence.ofDerived top urs (htop.trans hurs.symm)
    (by rw [htop]; decide)
  have hrows : instanceRowPolynomial (2 ^ urs.k) top.omega (top.fixedRows.getD column.val []) =
      rowPolynomial (omegaOf 11) (plonkKeygenFixedRows top column) := by
    rw [instanceRowPolynomial, TopLevelCircuit.omega, htop, hurs]
    rfl
  rw [hcoherent column.val hcolumn, lagrangeCommitInstance_eq_polynomialCommitment, hrows]

/-- The actual compiler's sigma commitment is the reference compiler-sigma polynomial commitment. -/
theorem plonkKeygenSigmaCommitment (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G) (htop : top.domainExponent = 11) (hurs : urs.k = 11)
    (column : Fin 15) (hcolumn : column.val < top.permutationColumnCount) :
    topLevelPermutationCommitment top urs column.val =
      polynomialCommitment urs.g urs.w
        (rowPolynomial (omegaOf 11) (plonkKeygenSigmaRows top column)) 1 := by
  have hrows : instanceRowPolynomial (2 ^ urs.k) (omegaOf urs.k)
      (topLevelPermutationRows top column.val) =
      rowPolynomial (omegaOf 11) (plonkKeygenSigmaRows top column) := by
    rw [instanceRowPolynomial, hurs, topLevelPermutationRows, htop]
    rfl
  rw [PermutationCommitmentCoherence.commitment_ofKeygen top urs (htop.trans hurs.symm)
    (LagrangePrefixSetup.ofDerived urs (by rw [hurs]; decide)) column.val hcolumn,
    lagrangeCommitInstance_eq_polynomialCommitment, hrows]

/-- The public-input commitment uses exactly the reference's zero-padded instance rows. -/
theorem plonkKeygenInstanceCommitment {actions : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput) (urs : URS G)
    (htop : top.domainExponent = 11) (hurs : urs.k = 11)
    (inputs : Fin actions → PublicInput Fp) (a : Fin actions) :
    top.instanceCommitment urs inputs a 0 =
      polynomialCommitment urs.g urs.w
        (rowPolynomial (omegaOf 11)
          (fun row : Fin 2048 => (top.publicInputRows (inputs a) ⟨0⟩).getD row.val 0)) 1 := by
  have hrows : instanceRowPolynomial (2 ^ urs.k) (top.toVerifierKey urs).omega
      (top.publicInputRows (inputs a) ⟨0⟩) =
      rowPolynomial (omegaOf 11)
        (fun row : Fin 2048 => (top.publicInputRows (inputs a) ⟨0⟩).getD row.val 0) := by
    rw [instanceRowPolynomial, TopLevelCircuit.toVerifierKey_omega,
      TopLevelCircuit.omega, htop, hurs]
    rfl
  unfold TopLevelCircuit.instanceCommitment
  rw [lagrangeCommitInstance_eq_polynomialCommitment, hrows]

end Zcash.Snark.ZeroKnowledge
