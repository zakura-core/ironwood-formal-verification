import Zcash.Snark.ZeroKnowledge.Sampling
import Zcash.Snark.ZeroKnowledge.MaskPolynomials
import Zcash.Snark.ZeroKnowledge.MaskSampling
import Zcash.Snark.ZeroKnowledge.IpaSampling
import Zcash.Snark.ZeroKnowledge.IpaSimulator
import Zcash.Snark.ZeroKnowledge.IpaVerifier
import Zcash.Meta.AxiomCheck

/-!
# Checked trust boundary of the zero-knowledge development

These pins bound the transitive proof dependencies to Lean's standard axioms. No native-code
axiom or admitted lemma is permitted. Probability distributions are intentionally noncomputable;
the finite sampling program and its declared tape sizes are checked as computable definitions.
`+choice` permits classical choice only in erased proof fields of a plain computable definition;
the checker still rejects noncomputable algorithmic content. No `+native` exemption is used.

The pinned results establish the field-sampling law, both masking constructions, and joint
simulation of the algebraic IPA stage under supplied challenges. They do not establish a
whole-prover simulator, Fiat–Shamir zero-knowledge, or a Rust-to-Lean refinement.
-/

assert_computable Zcash.Snark.ZeroKnowledge.fieldSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.wordSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.sampleFieldsWith

assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample
assert_axioms Zcash.Snark.ZeroKnowledge.idealFieldSample
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_apply
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_weightedBias
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_bias_le
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_remainder_pos
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_zero_gt_light
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_ne_ideal
assert_axioms Zcash.Snark.ZeroKnowledge.fieldSample_ne_zero
assert_axioms Zcash.Snark.ZeroKnowledge.wordSampleCount_one
assert_axioms Zcash.Snark.ZeroKnowledge.wordSampleCount_two
assert_axioms Zcash.Snark.ZeroKnowledge.weightedBias_symm
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_queryBound
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sampleFieldsWith_error_bound
assert_axioms Zcash.Snark.ZeroKnowledge.sampledAttempt_error_bound

-- Common #225: derive the sparse polynomial and the full scalar from the recursive fold.
assert_computable Zcash.Snark.ZeroKnowledge.coefficientFold +choice
assert_computable Zcash.Snark.ZeroKnowledge.foldByRounds +choice
assert_computable Zcash.Snark.ZeroKnowledge.sparseIpaCoefficients +choice
assert_computable Zcash.Snark.ZeroKnowledge.sparseIpaPolynomial +choice
assert_computable Zcash.Snark.ZeroKnowledge.maskedIpaScalar +choice
assert_axioms Zcash.Snark.ZeroKnowledge.foldByRounds_eq_coefficientFold
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientFold_powerIndex
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientFold_eq_evaluation
assert_axioms Zcash.Snark.ZeroKnowledge.foldByRounds_eq_evaluation
assert_axioms Zcash.Snark.ZeroKnowledge.coeffsToPoly_sparseIpaCoefficients
assert_axioms Zcash.Snark.ZeroKnowledge.sparseIpaPolynomial_eval_root
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientEvaluation_sparseIpaCoefficients
assert_axioms Zcash.Snark.ZeroKnowledge.coefficientFold_sparseIpaCoefficients
assert_axioms Zcash.Snark.ZeroKnowledge.maskedIpaScalar_eq
assert_axioms Zcash.Snark.ZeroKnowledge.maskedIpaScalar_eq_zero_of_evaluation
assert_axioms Zcash.Snark.ZeroKnowledge.affineLinearForm_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.sparseIpaScalar_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.maskedIpaScalar_simulates
assert_axioms Zcash.Snark.ZeroKnowledge.actualSparseIpaScalar_error_bound

-- Common #267: retain the already disclosed evaluation and the unit-weight contribution.
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskPair
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskView
assert_computable Zcash.Snark.ZeroKnowledge.linearMaskPolynomial +choice
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskPolynomial_evaluations
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskPair_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.linearMaskView_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.horner_last_unit_weight
assert_axioms Zcash.Snark.ZeroKnowledge.horner_last_at_zero
assert_axioms Zcash.Snark.ZeroKnowledge.actualLinearMaskView_error_bound

-- The joint IPA view includes the actual cross terms and the aggregate blind, not just `c`.
assert_computable Zcash.Snark.ZeroKnowledge.publicFold
assert_computable Zcash.Snark.ZeroKnowledge.ipaCrossTerms +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaCoreMessages +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaMessageSum +choice
assert_computable Zcash.Snark.ZeroKnowledge.blindIpaMessages
assert_computable Zcash.Snark.ZeroKnowledge.ipaFinalBlind +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaMaskedVector +choice
assert_computable Zcash.Snark.ZeroKnowledge.honestIpaTranscript +choice
assert_computable Zcash.Snark.ZeroKnowledge.completeIpaTranscript +choice
assert_computable Zcash.Snark.ZeroKnowledge.chooseIpaScalar +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaSimulatorFromCoins +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaSampleCount
assert_computable Zcash.Snark.ZeroKnowledge.ipaTapeEquiv +choice
assert_computable Zcash.Snark.ZeroKnowledge.ipaTranscriptFromTape +choice
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCrossTerms_equation
assert_axioms Zcash.Snark.ZeroKnowledge.ipaCoreMessages_equation
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMessageSum_blind
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMaskedVector_eval_zero
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscript_verifies
assert_axioms Zcash.Snark.ZeroKnowledge.completeIpaTranscript_verifies
assert_axioms Zcash.Snark.ZeroKnowledge.IpaTranscript.eq_complete_of_verifies
assert_axioms Zcash.Snark.ZeroKnowledge.ipaBlindsEquiv_apply
assert_axioms Zcash.Snark.ZeroKnowledge.honestIpaTranscript_fixed_mask
assert_axioms Zcash.Snark.ZeroKnowledge.idealIpa_simulation_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.blinding_bijective_of_card_eq
assert_axioms Zcash.Snark.ZeroKnowledge.chooseIpaScalar_uniform
assert_axioms Zcash.Snark.ZeroKnowledge.idealIpaSimulatorFromFieldCoins_eq
assert_axioms Zcash.Snark.ZeroKnowledge.ipaSampleCount_eq
assert_axioms Zcash.Snark.ZeroKnowledge.ipaSampleCount_eleven
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTapeEquiv_alphas
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTapeEquiv_maskBlind
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTapeEquiv_roundBlinds
assert_axioms Zcash.Snark.ZeroKnowledge.uniformTapeIpa_eq_idealProver
assert_axioms Zcash.Snark.ZeroKnowledge.sampledIpa_simulation_error_bound

-- The simulated raw equation is the existing verifier's final IPA assembly.
assert_computable Zcash.Snark.ZeroKnowledge.IpaPublic.ofMsm +choice
assert_computable Zcash.Snark.ZeroKnowledge.IpaTranscript.ofProofString
assert_axioms Zcash.Snark.ZeroKnowledge.publicFold_eq_foldAll
assert_axioms Zcash.Snark.ZeroKnowledge.computeS_gterm_publicFold
assert_axioms Zcash.Snark.ZeroKnowledge.publicFold_evalVector
assert_axioms Zcash.Snark.ZeroKnowledge.ipaMessageSum_eq_roundSum
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTranscript_verifier_capstone
assert_axioms Zcash.Snark.ZeroKnowledge.ipaTranscript_assembleFinalMsm
