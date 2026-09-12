import Zcash.Snark.ZeroKnowledge.PlonkKeygenSigmaRows
import Zcash.Snark.ZeroKnowledge.PlonkCopyWitness
import Zcash.Snark.ZeroKnowledge.PlonkKeygenFixed

/-!
# The public sigma profile follows from compiler key generation

The public sigma polynomials interpolate the compiler's actual permutation table.
The key's sigma-query indices and naming constants identify their evaluations with
the replayed packed-cell names. Original copy values are the witness-validity
premise; key generation supplies sigma coherence.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp deltaFp omegaOf)
open Halo2

/-- Each packed entry queries the sigma column at its global permutation-column index. -/
def plonkCopySigmaIndices (chunks : List (List (ColumnRef × ℕ))) : Prop :=
  ∀ (chunk : Fin 3) (column : Fin (chunks.getD chunk.val []).length),
    ((chunks.getD chunk.val []).getD column.val (.advice 0, 0)).2 = chunk.val * 7 + column.val

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- Compiler-produced public sigma polynomials have the exact packed replay labels. -/
theorem plonkKeygenSigmaCoherent {actions : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    (hcolumns : top.permutationColumnCount = 15) (hrows : Halo2.usedRows top.operations ≤ 2042)
    (chunks : List (List (ColumnRef × ℕ))) (hwidth : plonkCopyChunkWidths chunks)
    (hindices : plonkCopySigmaIndices chunks)
    (delta : Fp) (stride : ℕ) (hdelta : delta = deltaFp) (hstride : stride = 7)
    (instances : Fin actions → Fin 2048 → Fp) (cell : PlonkCopyCell chunks) :
    plonkCopyCellSigma (plonkKeygenPublicPolynomials top instances (plonkKeygenSigmaRows top)) cell =
      plonkCopyCellName delta stride
        (replayKeygenPermutation (plonkKeygenCopies top hcolumns hrows chunks hwidth) cell) := by
  have hindex : (plonkCopyCellEntry cell).2 = (plonkCopyCellRaw cell).1 :=
    hindices cell.1 cell.2.2
  have hindexLt : (plonkCopyCellEntry cell).2 < 15 := by
    rw [hindex]
    exact (plonkCopyCellToFull 15 rfl chunks hwidth cell).1.isLt
  simp only [plonkCopyCellSigma, finFn, hindexLt, ↓reduceDIte]
  rw [plonkKeygenPublicPolynomials]
  refine (plonkPublicPolynomialsFromRows_sigma_eval instances (plonkKeygenFixedRows top)
    (plonkKeygenSigmaRows top) ⟨_, hindexLt⟩
    ⟨cell.2.1.val, cell.2.1.isLt.trans_le (by decide)⟩).trans ?_
  dsimp only [plonkKeygenSigmaRows]
  rw [hindex, plonkKeygenSigmaRows_eq_replay top hcolumns hrows chunks hwidth cell]
  simp only [plonkCopyCellName, plonkCopyCellRaw, hdelta, hstride, pow_add]
  ring

/-- Original copy equations suffice once compiler keygen supplies the sigma polynomials. -/
theorem plonkKeygenCopyWitness_of_values {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G)
    (top : TopLevelCircuit Fp Config PublicInput)
    (hcolumns : top.permutationColumnCount = 15) (hrows : Halo2.usedRows top.operations ≤ 2042)
    (hwidth : plonkCopyChunkWidths vk.permutationChunks)
    (hindices : plonkCopySigmaIndices vk.permutationChunks)
    (hdelta : vk.delta = deltaFp) (hstride : vk.chunkLen = 7)
    (hqueries : plonkPermutationQueriesUnrotated vk.permutationChunks = true)
    (instances : Fin actions → Fin 2048 → Fp) (witness : Fin actions → Fin 10 → Fin 2048 → Fp) :
    let pub := plonkKeygenPublicPolynomials top instances (plonkKeygenSigmaRows top)
    let copies := plonkKeygenCopies top hcolumns hrows vk.permutationChunks hwidth
    (∀ a : Fin actions, ∀ pair ∈ copies,
      (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.1).1 =
        (plonkCopyCellPair pub (plonkUnmaskedAdviceRows witness) a vk.permutationChunks pair.2).1) →
      PlonkCopyWitness vk pub witness copies := by
  intro pub copies hvalues
  exact ⟨hqueries, plonkKeygenSigmaCoherent top hcolumns hrows vk.permutationChunks hwidth hindices
    vk.delta vk.chunkLen hdelta hstride instances, hvalues⟩

end Zcash.Snark.ZeroKnowledge
