import Zcash.Snark.ZeroKnowledge.PlonkFresh
import Zcash.Snark.ZeroKnowledge.PlonkDigest
import Zcash.Snark.ZeroKnowledge.PlonkAttempt

/-!
# The first private commitment in the joint simulator

The joint simulator samples its pre-IPA point family uniformly, independently
of all field challenges, including exceptional ones. Recovering raw digests
does not change this marginal. Every nonempty Action proof begins with the
first advice commitment, so this point anchors every later hash query.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)

/-- Conditional raw-digest recovery preserves the entire original view as its marginal. -/
theorem attachPlonkDigests_forget {k : ℕ} {V : Type*} (law : PMF (Challenges k Fp × V)) :
    (attachPlonkDigests law).map Prod.snd = law := by
  simp only [attachPlonkDigests, liftDigestTapeView, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hconstant (view : Challenges k Fp × V) :
      (digestTapeFiberSample (plonkChallengeFields view.1)).map (fun _ => view) = PMF.pure view :=
    PMF.map_const _ _
  simp_rw [hconstant]
  exact PMF.bind_pure _

/-- A positive Action count supplies an actual first private advice commitment in the message trace. -/
theorem plonkAttemptTrace_firstAdvice {actions k : ℕ} {F G : Type*}
    (proof : ProofString (plonkProofShape actions k) F G) (hpositive : 0 < actions) :
    ∃ rest, plonkAttemptTrace proof =
      .point (proof.adviceCommitments ⟨0, hpositive⟩ (0 : Fin 10)) :: rest := by
  have hhead : ∃ rest, absorbPoints2 (F := F) proof.adviceCommitments =
      .point (proof.adviceCommitments ⟨0, hpositive⟩ (0 : Fin 10)) :: rest := by
    cases actions with
    | zero => omega
    | succ actions =>
      change ∃ rest, @absorbPoints2 F G (actions + 1) 10 proof.adviceCommitments =
        .point (proof.adviceCommitments ⟨0, hpositive⟩ (0 : Fin 10)) :: rest
      simp only [absorbPoints2, List.ofFn_succ, List.flatten_cons, absorbPoints, List.cons_append]
      exact ⟨_, rfl⟩
  obtain ⟨rest, hrest⟩ := hhead
  simp only [plonkAttemptTrace, preIpaTranscript, List.nil_append, hrest, List.cons_append]
  exact ⟨_, rfl⟩

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The pre-IPA simulator's complete point family has exactly the uniform-vector marginal. -/
theorem preIpaMaskSimulator_points (d columns commitments : ℕ) :
    (preIpaMaskSimulator (G := G) d columns commitments).map Prod.fst =
      PMF.uniformOfFintype (Fin commitments → G) := by
  simp only [preIpaMaskSimulator, Zcash.independentProductPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hconstant (points : Fin commitments → G) :
      (PMF.uniformOfFintype (Fp × Fp)).map (fun _ => points) = PMF.pure points := PMF.map_const _ _
  simp_rw [hconstant]
  simp only [PMF.bind_const, PMF.bind_pure]

variable [Module Fp G]

/-- Simulating the IPA preserves that point-family marginal for every public challenge record. -/
theorem idealPlonkJointSimulator_points {actions : ℕ} (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (expectedHx : (PrivateColumnId actions → Fin 5 → Fp) → Fp) :
    (idealPlonkJointSimulator urs pub x x1 x2 x4 q xi z rounds expectedHx).map (fun view => view.1.1) =
      PMF.uniformOfFintype (Fin (22 * actions + 10) → G) := by
  simp only [idealPlonkJointSimulator, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hconstant (view : PreIpaMaskView 5 (22 * actions + 10) G) :
      (idealIpaSimulator (plonkPublicIpaInput urs pub x x1 x2 x4 q xi z rounds expectedHx view)).map
        (fun _ => view.1) = PMF.pure view.1 := PMF.map_const _ _
  simp_rw [hconstant]
  exact preIpaMaskSimulator_points _ _ _

/-- Every selected advice commitment is uniform in the simulator, without challenge exclusions. -/
theorem idealPlonkVerifierSimulator_advice {actions : ℕ} (urs : URS G)
    (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges urs.k Fp) (action : Fin actions) (column : Fin 10) :
    (idealPlonkVerifierSimulator urs vk pub ch).map (fun proof => proof.adviceCommitments action column) =
      PMF.uniformOfFintype G := by
  let index := Fin.castAdd 10 (privateColumnIndex (.advice action column))
  have h := congrArg (PMF.map (fun points : Fin (22 * actions + 10) → G => points index))
    (idealPlonkJointSimulator_points urs pub ch.x ch.x1 ch.x2 ch.x4 ch.x3 ch.xi ch.z
      ch.ipaRound (plonkVerifierHx vk pub ch))
  simpa only [PMF.map_comp, Function.comp_def, Zcash.map_eval_uniformOfFintype,
    idealPlonkVerifierSimulator, plonkProofFromJointView, plonkProofString, plonkColumnEntry, index] using h

/-- Mixing over arbitrary verifier challenges preserves the same uniform advice commitment. -/
theorem freshPlonkVerifierSimulator_advice {actions : ℕ} (urs : URS G)
    (law : PMF (Challenges urs.k Fp)) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (action : Fin actions) (column : Fin 10) :
    (freshPlonkVerifierSimulator urs law vk pub).map (fun view => view.2.adviceCommitments action column) =
      PMF.uniformOfFintype G := by
  simp only [freshPlonkVerifierSimulator, PMF.map_bind, PMF.map_comp, Function.comp_def]
  simp_rw [idealPlonkVerifierSimulator_advice]
  exact PMF.bind_const _ _

/-- Keeping the raw challenge responses also leaves the simulator's advice commitment uniform. -/
theorem digestPlonkVerifierSimulator_advice {actions : ℕ} (urs : URS G)
    (law : PMF (Challenges urs.k Fp)) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (action : Fin actions) (column : Fin 10) :
    (attachPlonkDigests (freshPlonkVerifierSimulator urs law vk pub)).map
        (fun view => view.2.2.adviceCommitments action column) = PMF.uniformOfFintype G := by
  have h := congrArg (PMF.map (fun view : PlonkFreshView actions urs.k G =>
    view.2.adviceCommitments action column))
    (attachPlonkDigests_forget (freshPlonkVerifierSimulator urs law vk pub))
  rw [PMF.map_comp] at h
  exact h.trans (freshPlonkVerifierSimulator_advice urs law vk pub action column)

end Zcash.Snark.ZeroKnowledge
