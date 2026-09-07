import Zcash.Snark.ZeroKnowledge.ActionConfiguration
import Zcash.Snark.ZeroKnowledge.PlonkKeygenSigma

/-!
# The actual Action key in the reference proof shape

The selector-compression count is the only layout premise. The configure program
supplies the complete query order and the exact permutation chunks. The key's
domain, naming constants, chunk widths, sigma indices, and unrotated copy queries
therefore follow from key generation, independently of captured-key data.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits.Action
open Zcash.Arithmetic (Fp URS omegaOf deltaFp)

/-- The actual compiler's ordered permutation-query references, grouped seven, seven, and one. -/
def actionReferencePermutationChunks : List (List (ColumnRef × ℕ)) :=
  [[(.instance 0, 0), (.advice 0, 1), (.advice 1, 2), (.advice 2, 3),
      (.advice 3, 4), (.advice 4, 5), (.advice 5, 6)],
    [(.advice 6, 7), (.advice 7, 8), (.advice 8, 9), (.advice 9, 10),
      (.fixed 0, 11), (.fixed 7, 12), (.fixed 8, 13)],
    [(.fixed 9, 14)]]

/-- The derived Action verifier uses precisely these permutation references and sigma indices. -/
theorem actionCircuit_permutationChunks_eq
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    actionCircuit.verifierCS.permutationChunks = actionReferencePermutationChunks := by
  change ((actionCircuit.permutationColumns.map fun column =>
    match column.kind with
    | .advice => ColumnRef.advice (actionCircuit.adviceQueryLayout.findIdx (· = (column.index, 0)))
    | .fixed => ColumnRef.fixed (actionCircuit.fixedQueryLayout.findIdx (· = (column.index, 0)))
    | .instance => ColumnRef.instance (actionCircuit.instanceQueryLayout.findIdx (· = (column.index, 0)))
    ).zipIdx).toChunks actionCircuit.chunkLen = _
  rw [actionCircuit_permutationColumns_eq, actionCircuit_adviceQueryLayout_eq,
    actionCircuit_fixedQueryLayout_of_selectorCount hpacked,
    actionCircuit_instanceQueryLayout_eq, actionCircuit_chunkLen_eq]
  decide +kernel

private theorem castKey_projection {G α : Type} {source target : CircuitShape}
    (hshape : source = target) (vk : VerifyingKey source Fp G)
    (projection : (shape : CircuitShape) → VerifyingKey shape Fp G → α) :
    projection target (hshape ▸ vk) = projection source vk := by
  cases hshape
  rfl

variable {G : Type} [AddCommGroup G] [Inhabited G] {actions : ℕ}

/-- Key generation for the actual Action, transported across its derived reference shape. -/
def actionReferenceKey (urs : URS G) (hk : urs.k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    VerifyingKey (plonkProofShape actions urs.k) Fp G :=
  actionCircuit_referenceShape actions urs.k hk hpacked ▸ actionCircuit.toVerifierKey urs

private theorem actionReferenceKey_projection (urs : URS G) (hk : urs.k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) {α : Type}
    (projection : (shape : CircuitShape) → VerifyingKey shape Fp G → α) :
    projection (plonkProofShape actions urs.k) (actionReferenceKey urs hk hpacked) =
      projection actionCircuit.shape (actionCircuit.toVerifierKey urs) :=
  castKey_projection _ _ projection

/-- Every query-layout condition for the reference key follows from configuration and the compression count. -/
theorem actionReferenceKey_queryLayout (urs : URS G) (hk : urs.k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    PlonkQueryLayout (actions := actions) (actionReferenceKey urs hk hpacked) := by
  constructor
  · exact (actionReferenceKey_projection urs hk hpacked (fun _ key => key.instanceQueryLayout)).trans
      actionCircuit_instanceQueryLayout_eq
  · exact (actionReferenceKey_projection urs hk hpacked (fun _ key => key.adviceQueryLayout)).trans
      actionCircuit_adviceQueryLayout_eq
  · exact (actionReferenceKey_projection urs hk hpacked (fun _ key => key.fixedQueryLayout)).trans
      (actionCircuit_fixedQueryLayout_of_selectorCount hpacked)
  · exact (actionReferenceKey_projection urs hk hpacked (fun _ key => key.blindingFactors)).trans
      actionCircuit_blindingFactors_eq

/-- The reference key retains the actual compiler's exact permutation chunks. -/
theorem actionReferenceKey_permutationChunks (urs : URS G) (hk : urs.k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    (actionReferenceKey (actions := actions) urs hk hpacked).permutationChunks =
      actionReferencePermutationChunks :=
  (actionReferenceKey_projection urs hk hpacked (fun _ key => key.permutationChunks)).trans
    (actionCircuit_permutationChunks_eq hpacked)

/-- The reference key's root and row count are the actual Action fitting domain. -/
theorem actionReferenceKey_domain (urs : URS G) (hk : urs.k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    (actionReferenceKey (actions := actions) urs hk hpacked).omega = omegaOf 11 ∧
      (actionReferenceKey (actions := actions) urs hk hpacked).n = 2048 := by
  constructor
  · rw [show (actionReferenceKey (actions := actions) urs hk hpacked).omega = actionCircuit.omega from
      actionReferenceKey_projection urs hk hpacked (fun _ key => key.omega)]
    rw [TopLevelCircuit.omega, actionCircuit_domainExponent_eq]
  · rw [show (actionReferenceKey (actions := actions) urs hk hpacked).n = actionCircuit.n from
      actionReferenceKey_projection urs hk hpacked (fun _ key => key.n)]
    rw [TopLevelCircuit.n, actionCircuit_domainExponent_eq]
    decide

/-- Sigma naming uses the protocol delta and the compiler-derived width seven. -/
theorem actionReferenceKey_sigmaNaming (urs : URS G) (hk : urs.k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    (actionReferenceKey (actions := actions) urs hk hpacked).delta = deltaFp ∧
      (actionReferenceKey (actions := actions) urs hk hpacked).chunkLen = 7 := by
  constructor
  · exact actionReferenceKey_projection urs hk hpacked (fun _ key => key.delta)
  · exact (actionReferenceKey_projection urs hk hpacked (fun _ key => key.chunkLen)).trans
      actionCircuit_chunkLen_eq

/-- The actual compiler key has the three required copy widths. -/
theorem actionReferenceKey_copyChunkWidths (urs : URS G) (hk : urs.k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    plonkCopyChunkWidths (actionReferenceKey (actions := actions) urs hk hpacked).permutationChunks := by
  rw [actionReferenceKey_permutationChunks]
  unfold plonkCopyChunkWidths
  decide +kernel

/-- Every compiler key sigma index is its global index in the fifteen-column family. -/
theorem actionReferenceKey_copySigmaIndices (urs : URS G) (hk : urs.k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    plonkCopySigmaIndices (actionReferenceKey (actions := actions) urs hk hpacked).permutationChunks := by
  rw [actionReferenceKey_permutationChunks]
  unfold plonkCopySigmaIndices
  decide +kernel

/-- All compiler copy queries use the unrotated advice-query prefix. -/
theorem actionReferenceKey_copyQueries (urs : URS G) (hk : urs.k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    plonkPermutationQueriesUnrotated
      (actionReferenceKey (actions := actions) urs hk hpacked).permutationChunks = true := by
  rw [actionReferenceKey_permutationChunks]
  decide +kernel

/-- The reference key has three permutation chunks containing fifteen columns altogether. -/
theorem actionReferenceKey_productShape (urs : URS G) (hk : urs.k = 11)
    (hpacked : actionCircuit.selectorMap.newFixedCols = 15) :
    (actionReferenceKey (actions := actions) urs hk hpacked).permutationChunks.length = 3 ∧
      (actionReferenceKey (actions := actions) urs hk hpacked).permutationChunks.flatten.length = 15 := by
  rw [actionReferenceKey_permutationChunks]
  decide +kernel

end Zcash.Snark.ZeroKnowledge
