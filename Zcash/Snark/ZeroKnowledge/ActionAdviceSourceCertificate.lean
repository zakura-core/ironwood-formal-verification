import Zcash.Snark.ZeroKnowledge.ActionAdviceReadPlan
import Zcash.Snark.ZeroKnowledge.ActionAdviceSourceAliasCheck

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action

/-- The generated assignment satisfies all original witness equations. -/
theorem actionWitnessAssignment_extendsWitnesses (inputs : PublicInputs Fp) (witness : PrivateWitness) :
    ExtendsWitnesses actionCircuit.placement
      (actionCircuit.proverEnvironment (actionWitnessAssignment inputs witness) (actionWitnessHints witness))
      actionCircuit.operations 0 := by
  exact topLevelAdviceAssignment_extendsWitnesses_of_sourceCertificate actionCircuit
    (initialPublicWitnessAssignment actionCircuit inputs) (actionWitnessHints witness)
    actionAdviceAliasPrograms actionAdviceSourceCertificate actionAdviceAliasPrograms_erase
    actionAdviceSource_aliasPlan actionAdviceSource_readPlan actionAdviceAliasPrograms_sources

end Zcash.Snark.ZeroKnowledge
