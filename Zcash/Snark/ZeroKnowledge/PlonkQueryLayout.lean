import Zcash.Snark.ZeroKnowledge.PlonkProofString
import Zcash.Snark.ZeroKnowledge.GroupingPattern
import Zcash.Snark.Fingerprint.Rational.GroupingTable

/-!
# The reference proof's verifier query pattern

The pattern retains every commitment ID and its point label, in the verifier's
flat query order. It forgets only commitment values and evaluations, which do not
determine the grouping. The key's query-layout conditions remain explicit here.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The four evaluation rotations in first-appearance order for a nonempty Action bundle. -/
def plonkQueryRotation : Fin 4 → ℤ := ![0, 1, -1, -6]

/-- Interpret an opening-point label using the verifier's actual rotation operation. -/
def plonkQueryPoint (omega x : Fp) (i : Fin 4) : Fp :=
  rotateOmega omega x (plonkQueryRotation i)

/-- The abstract query labels name precisely the first four points of the masking experiment. -/
theorem plonkQueryPoint_eq_observation (omega x q : Fp) (i : Fin 4) :
    plonkQueryPoint omega x i = plonkObservationPoints omega x q i.castSucc := by
  fin_cases i <;> simp [plonkQueryPoint, plonkQueryRotation, rotateOmega, plonkObservationPoints, zpow_ofNat]

/-- The existing masking experiment's distinctness premise makes the label interpretation injective. -/
theorem plonkQueryPoint_injective (omega x q : Fp)
    (hpoints : Function.Injective (plonkObservationPoints omega x q)) :
    Function.Injective (plonkQueryPoint omega x) := by
  intro i j hij
  simp only [plonkQueryPoint_eq_observation omega x q] at hij
  exact Fin.castSucc_injective 4 (hpoints hij)

/-- The key-side query ordering and final permutation rotation of the pinned protocol. -/
structure PlonkQueryLayout {actions k : ℕ} {G : Type*}
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) : Prop where
  instances : vk.instanceQueryLayout = [(0, 0)]
  advice : vk.adviceQueryLayout = List.ofFn (fun j : Fin 25 =>
    ((plonkAdviceQueryOrder j).1.val, plonkQueryRotation (plonkAdviceQueryOrder j).2.castSucc))
  fixed : vk.fixedQueryLayout = List.ofFn (fun j : Fin 29 => ((plonkFixedQueryOrder j).val, 0))
  blinding : vk.blindingFactors = 5

/-- One Action's flat opening queries, before shared fixed, sigma, and vanishing queries. -/
def plonkPerActionQuerySpine (a : ℕ) : List (CommitmentId × Fin 4) :=
  [(.instanceCol a 0, 0)] ++
    List.ofFn (fun j : Fin 25 =>
      (.adviceCol a (plonkAdviceQueryOrder j).1.val, (plonkAdviceQueryOrder j).2.castSucc)) ++
    (List.ofFn (fun s : Fin 3 => [(.permProduct a s.val, 0), (.permProduct a s.val, 1)])).flatten ++
    [(.permProduct a 1, 3), (.permProduct a 0, 3)] ++
    (List.ofFn (fun l : Fin 3 =>
      [(.lookupProduct a l.val, 0), (.lookupPermInput a l.val, 0), (.lookupPermTable a l.val, 0),
        (.lookupPermInput a l.val, 2), (.lookupProduct a l.val, 1)])).flatten

/-- The full flat commitment-ID and point-label stream, for any number of Actions. -/
def plonkQuerySpine (actions : ℕ) : List (CommitmentId × Fin 4) :=
  (List.ofFn (fun a : Fin actions => plonkPerActionQuerySpine a.val)).flatten ++
    List.ofFn (fun j : Fin 29 => (.fixedCol (plonkFixedQueryOrder j).val, 0)) ++
    List.ofFn (fun j : Fin 15 => (.permCommon j.val, 0)) ++ [(.vanishingH, 0), (.randomPoly, 0)]

/-- Feed the finite point labels and commitment IDs to the actual grouping algorithm. -/
def plonkQueryPattern (actions k : ℕ) : List (VerifierQuery k (Fin 4) Unit) :=
  (plonkQuerySpine actions).map fun entry =>
    { point := entry.2, commitment := .point (), eval := 0, commId := entry.1 }

/-- The complete reference proof produces exactly the declared flat verifier query pattern. -/
theorem plonkProofFromJointView_querySpine {actions k : ℕ} {G : Type*} [Inhabited G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G) :
    (assembleQueries vk instanceCommitment (plonkProofFromJointView pub ch.x ch.x1 view) ch).map
        (fun query : VerifierQuery k Fp G => (query.commId, query.point)) =
      (plonkQuerySpine actions).map (fun entry => (entry.1, plonkQueryPoint vk.omega ch.x entry.2)) := by
  dsimp only [plonkProofShape, FixtureMax.shape]
  simp [assembleQueries, hlayout.instances, hlayout.advice, hlayout.fixed, hlayout.blinding,
    columnQueries, permutationQueries, lookupQueries, permutationCommonQueries, vanishingQueries,
    plonkProofFromJointView, plonkProofString, plonkProofShape, FixtureMax.shape,
    plonkQuerySpine, plonkPerActionQuerySpine, plonkQueryPoint, plonkQueryRotation,
    plonkAdviceQueryOrder, plonkFixedQueryOrder, List.map_append, List.map_flatten,
    List.range_succ, Function.comp_def, rotateOmega]

/-- The actual ID and point streams match the finite pattern, including exceptional challenges. -/
theorem plonkProofFromJointView_queryPattern {actions k : ℕ} {G : Type*} [Inhabited G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G) :
    let queries := assembleQueries vk instanceCommitment (plonkProofFromJointView pub ch.x ch.x1 view) ch
    queries.map (·.commId) = (plonkQueryPattern actions k).map (·.commId) ∧
      queries.map (·.point) = (plonkQueryPattern actions k).map
        (fun query => plonkQueryPoint vk.omega ch.x query.point) := by
  have h := plonkProofFromJointView_querySpine vk hlayout pub instanceCommitment ch view
  constructor
  · simpa only [List.map_map, Function.comp_def, plonkQueryPattern] using
      congrArg (List.map Prod.fst) h
  · simpa only [List.map_map, Function.comp_def, plonkQueryPattern] using
      congrArg (List.map Prod.snd) h

/-- For distinct interpreted query points, the actual verifier has exactly the pattern's ID groups. -/
theorem plonkProofFromJointView_groupingIds {actions k : ℕ} {G : Type*}
    [Inhabited G] [DecidableEq G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x)) :
    (constructIntermediateSets (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch)).ids =
        (constructIntermediateSets (plonkQueryPattern actions k)).ids := by
  have h := plonkProofFromJointView_queryPattern vk hlayout pub instanceCommitment ch view
  exact groupingPattern_ids _ _ _ hpoints h.1 h.2

/-- The actual verifier's node order is the finite pattern's order interpreted in the field. -/
theorem plonkProofFromJointView_groupingNodes {actions k : ℕ} {G : Type*}
    [Inhabited G] [DecidableEq G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x)) :
    (constructIntermediateSets (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch)).points =
        (constructIntermediateSets (plonkQueryPattern actions k)).points.map
          (List.map (plonkQueryPoint vk.omega ch.x)) := by
  have h := plonkProofFromJointView_queryPattern vk hlayout pub instanceCommitment ch view
  exact groupingPattern_nodes _ _ _ hpoints h.1 h.2

/-- The actual duplicate-query check agrees with the finite pattern on distinct query points. -/
theorem plonkProofFromJointView_duplicateQueries {actions k : ℕ} {G : Type*} [Inhabited G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (hlayout : PlonkQueryLayout vk)
    (pub : PlonkPublicPolynomials actions) (instanceCommitment : Fin actions → ℕ → G)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G)
    (hpoints : Function.Injective (plonkQueryPoint vk.omega ch.x)) :
    hasDuplicateCommitmentPoint (assembleQueries vk instanceCommitment
      (plonkProofFromJointView pub ch.x ch.x1 view) ch) =
        hasDuplicateCommitmentPoint (plonkQueryPattern actions k) := by
  have h := plonkProofFromJointView_queryPattern vk hlayout pub instanceCommitment ch view
  exact groupingPattern_duplicates _ _ _ hpoints h.1 h.2

end Zcash.Snark.ZeroKnowledge
