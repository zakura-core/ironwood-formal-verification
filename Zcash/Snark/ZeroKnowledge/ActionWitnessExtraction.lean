import Zcash.Snark.ZeroKnowledge.ActionDirectHintExtraction
import Zcash.Snark.ZeroKnowledge.ActionScalarHintExtraction
import Zcash.Snark.ZeroKnowledge.ActionMerkleHintExtraction
import Zcash.Snark.ZeroKnowledge.ActionWitnessReadings
import Zcash.Snark.ZeroKnowledge.ActionWitnessRows

/-!
# Recovering the application's private Action readings

The original full Action witness equations imply agreement with the normalized
application witness on every value inspected by the existing honest-prover
preconditions. This assembles the original field and point loaders, all five
scalar/window pairs, and the 32 used Merkle readings. It uses the actual fixed
hint program and actual generated assignment, including full-range scalar decoding.

The source certificate must independently establish the witness equations. No
gate validity, successful proof attempt, or verifier acceptance is assumed.
-/

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 8192
set_option linter.constructorNameAsVariable false

/-- The complete original Action witness equations include the original base synthesis. -/
theorem actionCircuit_base_extendsWitnesses (env : Placed ProverEnvironment Fp)
    (hw : ExtendsWitnesses env.place env.env actionCircuit.operations 0) :
    ExtendsWitnesses env.place env.env
      ((Circuit.synthesizeBase Specs.Sinsemilla.orchardGenerators orchardBases
        Circuit.hintWitnesses actionConfig).operations 0) 0 := by
  rw [Internal.actionCircuit_eq_impl] at hw
  change ExtendsWitnesses env.place env.env
    ((Circuit.mainPost Specs.Sinsemilla.orchardGenerators orchardBases actionConfig ()).operations 0) 0 at hw
  simp only [Circuit.mainPost, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil, circuit_norm] at hw
  have hbase := hw.1
  rw [FormalCircuit.call_operations] at hbase
  exact hbase

/-- Original witness consistency recovers every private reading needed by completeness. -/
theorem actionWitnessAssignment_readAgreement_of_extendsWitnesses
    (inputs : PublicInputs Fp) (witness : PrivateWitness)
    (hw : ExtendsWitnesses actionCircuit.placement
      (actionCircuit.proverEnvironment (actionWitnessAssignment inputs witness) (actionWitnessHints witness))
      actionCircuit.operations 0) :
    ActionWitnessReadAgreement
      (PrivateWitness.ofActionData (Circuit.extractPost actionConfig () 0
        (actionCircuit.placedEnvironment (actionWitnessAssignment inputs witness))))
      (normalizeActionWitness witness) := by
  let env := actionCircuit.placedProverEnvironment
    (actionWitnessAssignment inputs witness) (actionWitnessHints witness)
  have hbase := actionCircuit_base_extendsWitnesses env hw
  obtain ⟨hpsi, hrho, hnk, hvo, hvn, hpsiNew, hmag, hsign,
    hcm, hgd, hak, hpkd, hgdNew, hpkdNew⟩ :=
    actionDirectHintCells_of_extendsWitnesses _ _ _ _ _ env hbase
  obtain ⟨hrcv, halpha, hrivk, hrcmOld, hrcmNew⟩ :=
    actionScalarWindowReadings_of_extendsWitnesses _ _ _ _ _ env hbase
  have hmerkle := actionMerkleHintCells_of_extendsWitnesses _ _ _ _ _ env hbase
  have hdecode := actionWitnessAssignment_hintData inputs witness
  simp only [Circuit.hintWitnesses, actionWitnessHintData, circuit_norm] at hdecode
  obtain ⟨dpsi, drho, dnk, dvo, dvn, dpsiNew, dmag, dsign,
    dcm, dgd, dak, dpkd, dgdNew, dpkdNew, _, _, _, _, _, dsib, dswap⟩ := hdecode
  obtain ⟨drcv, dalpha, drivk, drcmOld, drcmNew⟩ :=
    actionWitnessAssignment_hintWindows inputs witness
  have scalarPair (windows : Vector Fp 85) (scalar : Fq)
      (h : windows = canonicalActionScalarWindows scalar) :
      (windows, Ecc.MulFixed.FullWidth.windowsScalar windows) =
        (canonicalActionScalarWindows scalar, scalar) := by
    rw [h, canonicalActionScalarWindows_reconstruct]
  constructor
  · with_unfolding_all exact hpsi.trans dpsi
  · with_unfolding_all exact hrho.trans drho
  · with_unfolding_all exact hnk.trans dnk
  · with_unfolding_all exact hvo.trans dvo
  · with_unfolding_all exact hvn.trans dvn
  · with_unfolding_all exact hpsiNew.trans dpsiNew
  · with_unfolding_all exact hmag.trans dmag
  · with_unfolding_all exact hsign.trans dsign
  · with_unfolding_all exact hcm.trans dcm
  · with_unfolding_all exact hgd.trans dgd
  · with_unfolding_all exact hak.trans dak
  · with_unfolding_all exact hpkd.trans dpkd
  · with_unfolding_all exact hgdNew.trans dgdNew
  · with_unfolding_all exact hpkdNew.trans dpkdNew
  · with_unfolding_all exact scalarPair _ _ (hrcv.trans drcv)
  · with_unfolding_all exact scalarPair _ _ (halpha.trans dalpha)
  · with_unfolding_all exact scalarPair _ _ (hrivk.trans drivk)
  · with_unfolding_all exact scalarPair _ _ (hrcmOld.trans drcmOld)
  · with_unfolding_all exact scalarPair _ _ (hrcmNew.trans drcmNew)
  · intro index hi
    change (Circuit.extract actionConfig Circuit.hintWitnesses 0
      ⟨env.place, env.env.toEnvironment⟩).merklePath index = canonicalActionMerklePath witness index
    rw [hmerkle index hi]
    have hsib := congrFun dsib index
    have hswap := congrFun dswap index
    simp only [actionMerkleSibling_eval] at hsib
    simp only [actionMerkleSwap_eval] at hswap
    with_unfolding_all
      change Circuit.hintWitnesses.merkleSwap index env = actionWitnessSide witness index at hswap
    apply Prod.ext
    · exact hsib
    · simp only [hswap, canonicalActionMerklePath, actionWitnessSide, dif_pos hi]

end Zcash.Snark.ZeroKnowledge
