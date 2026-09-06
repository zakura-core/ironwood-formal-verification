import Zcash.Snark.ZeroKnowledge.MultiopenIpa

/-!
# The pinned five groups produce the IPA polynomial and blind

This instantiates the multi-opening algebra with the exact groups in `PlonkOpening`.
Public instance, fixed, and permutation-column commitments use blind one; `H_x` inherits
the weighted sum of the eight quotient-piece blinds. All other blinds follow their
private columns. No independence of the incoming IPA blind is assumed.

The computed group claims are actual polynomial evaluations. The separate obligation
that the complete verifier infers the same `H_x(x)` and routes these groups from its
proof string is not discharged by the results here.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp omegaOf URS)
open CompPoly
open Zcash.Common
open scoped ENNReal

/-- Point sets in the pinned group order. The later point `q` is not one of their nodes. -/
def plonkOpeningPointSets (omega x : Fp) : Fin 5 → List Fp :=
  ![[x], [x, x * omega], [x, x * omega, x * omega⁻¹],
    [x, x * omega, x * (omega ^ 6)⁻¹], [x, x * omega⁻¹]]

private def plonkOpeningPointIndices : Fin 5 → List (Fin 5) :=
  ![[0], [0, 1], [0, 1, 2], [0, 1, 3], [0, 2]]

private theorem plonkOpeningPointSets_eq_map (omega x q : Fp) (i : Fin 5) :
    plonkOpeningPointSets omega x i =
      (plonkOpeningPointIndices i).map (plonkObservationPoints omega x q) := by
  fin_cases i <;> rfl

/-- The common five-point distinctness condition supplies distinct nodes for every group. -/
theorem plonkOpeningPointSets_nodup (omega x q : Fp)
    (hpoints : Function.Injective (plonkObservationPoints omega x q)) (i : Fin 5) :
    (plonkOpeningPointSets omega x i).Nodup := by
  rw [plonkOpeningPointSets_eq_map omega x q]
  apply List.Nodup.map hpoints
  fin_cases i <;> decide

/-- The same condition makes every denominator at the later point nonzero. -/
theorem plonkOpeningPointSets_away (omega x q : Fp)
    (hpoints : Function.Injective (plonkObservationPoints omega x q)) (i : Fin 5) :
    q ∉ plonkOpeningPointSets omega x i := by
  rw [plonkOpeningPointSets_eq_map omega x q]
  intro hq
  obtain ⟨j, hj, heq⟩ := List.mem_map.mp hq
  have hj4 : j = 4 := hpoints heq
  have h4 : (4 : Fin 5) ∉ plonkOpeningPointIndices i := by fin_cases i <;> decide
  exact h4 (hj4 ▸ hj)

/-- Every pinned node list is nonempty and contains at most three points. -/
theorem plonkOpeningPointSets_length (omega x : Fp) (i : Fin 5) :
    0 < (plonkOpeningPointSets omega x i).length ∧
      (plonkOpeningPointSets omega x i).length ≤ 3 := by
  fin_cases i <;> simp [plonkOpeningPointSets]

/-- Commitment blinds already sampled before the IPA begins. -/
structure PlonkCommitmentBlinds (actions : ℕ) where
  columns : PrivateColumnId actions → Fp
  linear : Fp
  pieces : Fin 8 → Fp
  quotientPrime : Fp

/-- The collapsed quotient inherits the same weights on its commitment blinds. -/
def plonkCollapsedQuotientBlind (x : Fp) (blinds : Fin 8 → Fp) : Fp :=
  ∑ j, x ^ (2048 * j.val) * blinds j

/-- Pair each opening polynomial with its actual blind before applying the Horner fold. -/
def plonkOpeningPairs {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x : Fp) (pieces : Fin 8 → CPoly)
    (coefficients : Fp × Fp) (blinds : PlonkCommitmentBlinds actions) : Fin 5 → List (CPoly × Fp) :=
  Fin.cons
    ((List.finRange actions).flatMap (fun a =>
      [(pub.instances a, 1)] ++ (List.finRange 3).map (fun l =>
        (privateColumnPolynomial rows (.lookupTable a l), blinds.columns (.lookupTable a l)))) ++
      (List.finRange 29).map (fun j => (pub.fixed (plonkFixedQueryOrder j), 1)) ++
      (List.finRange 15).map (fun j => (pub.sigma j, 1)) ++
      [(plonkCollapsedQuotient x pieces, plonkCollapsedQuotientBlind x blinds.pieces),
        (linearMaskPolynomial coefficients, blinds.linear)])
    (fun i => (plonkPrivateGroupMembers actions i).map (fun id =>
      (privateColumnPolynomial rows id, blinds.columns id)))

/-- Pairing blinds preserves the exact polynomial order, including the last linear mask. -/
theorem plonkOpeningPairs_polynomials {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x : Fp) (pieces : Fin 8 → CPoly)
    (coefficients : Fp × Fp) (blinds : PlonkCommitmentBlinds actions) (i : Fin 5) :
    (plonkOpeningPairs pub rows x pieces coefficients blinds i).map Prod.fst =
      plonkOpeningGroups pub rows x pieces coefficients i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [plonkOpeningPairs, plonkOpeningGroups, plonkFirstGroupPrefix,
      List.map_flatMap, List.append_assoc, Function.comp_def]
  · simp [plonkOpeningPairs, plonkOpeningGroups, Function.comp_def]

/-- All five collapsed polynomials, point sets, and inherited blinds. -/
def plonkBlindedOpeningGroup {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x x1 : Fp) (pieces : Fin 8 → CPoly)
    (coefficients : Fp × Fp) (blinds : PlonkCommitmentBlinds actions) (i : Fin 5) :
    BlindedOpeningGroup where
  polynomial := plonkOpeningPolynomials pub rows x x1 pieces coefficients i
  points := plonkOpeningPointSets (omegaOf 11) x i
  blind := plonkScalarFold x1 ((plonkOpeningPairs pub rows x pieces coefficients blinds i).map Prod.snd)

/-- Enumerate the five groups in the order supplied to both later Horner folds. -/
def plonkBlindedOpeningGroups {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x x1 : Fp) (pieces : Fin 8 → CPoly)
    (coefficients : Fp × Fp) (blinds : PlonkCommitmentBlinds actions) : List BlindedOpeningGroup :=
  List.ofFn (plonkBlindedOpeningGroup pub rows x x1 pieces coefficients blinds)

section Commitments

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- `H_x` is exactly the weighted combination of the eight public quotient commitments. -/
theorem plonkCollapsedQuotient_commitment {n : ℕ} (generators : Fin n → G) (W : G)
    (x : Fp) (pieces : Fin 8 → CPoly) (blinds : Fin 8 → Fp) :
    polynomialCommitment generators W (plonkCollapsedQuotient x pieces)
        (plonkCollapsedQuotientBlind x blinds) =
      ∑ j, x ^ (2048 * j.val) • polynomialCommitment generators W (pieces j) (blinds j) :=
  polynomialCommitment_sum generators W (fun j : Fin 8 => x ^ (2048 * j.val)) pieces blinds

/-- The group's coefficient commitment agrees with folding its members' commitments. -/
theorem plonkBlindedOpeningGroup_commitment {n actions : ℕ} (generators : Fin n → G) (W : G)
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048) (x x1 : Fp)
    (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp) (blinds : PlonkCommitmentBlinds actions)
    (i : Fin 5) :
    let group := plonkBlindedOpeningGroup pub rows x x1 pieces coefficients blinds i
    polynomialCommitment generators W group.polynomial group.blind =
      commitmentHornerFold x1 ((plonkOpeningPairs pub rows x pieces coefficients blinds i).map
        fun pair => polynomialCommitment generators W pair.1 pair.2) := by
  have h := polynomialCommitment_fold generators W x1
    (plonkOpeningPairs pub rows x pieces coefficients blinds i)
  rw [plonkOpeningPairs_polynomials] at h
  exact h

end Commitments

/-- Degree facts required of the supplied public polynomials and quotient pieces. -/
structure PlonkDegreeBounds {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (pieces : Fin 8 → CPoly) : Prop where
  instances : ∀ a, (pub.instances a).natDegree < 2048
  fixed : ∀ j, (pub.fixed j).natDegree < 2048
  sigma : ∀ j, (pub.sigma j).natDegree < 2048
  quotient : ∀ j, (pieces j).natDegree < 2048

/-- Every private column fits the IPA vector, including totalized missing-column lookup. -/
theorem privateColumnPolynomial_natDegree_lt {actions : ℕ} (rows : ColumnHistory 2048)
    (id : PrivateColumnId actions) : (privateColumnPolynomial rows id).natDegree < 2048 := by
  have hall : ∀ poly ∈ rows.map (rowPolynomial (omegaOf 11)), poly.natDegree < 2048 := by
    intro poly hpoly
    obtain ⟨values, _, rfl⟩ := List.mem_map.mp hpoly
    exact rowPolynomial_natDegree_lt (omegaOf_rows_injective 11 (by decide)) (by decide)
  unfold privateColumnPolynomial
  by_cases hi : (privateColumnOrder actions).idxOf id < (rows.map (rowPolynomial (omegaOf 11))).length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hall _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    simp

/-- A scalar-weighted collapse of the eight pieces retains the strict degree bound. -/
theorem plonkCollapsedQuotient_natDegree_lt (x : Fp) (pieces : Fin 8 → CPoly)
    (hpieces : ∀ j, (pieces j).natDegree < 2048) :
    (plonkCollapsedQuotient x pieces).natDegree < 2048 := by
  rw [plonkCollapsedQuotient, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_sum]
  apply lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_) (by decide : 2047 < 2048)
  intro j _
  rw [CPolynomial.toPoly_mul, CPolynomial.C_toPoly]
  have h := lt_of_le_of_lt (Polynomial.natDegree_C_mul_le (x ^ (2048 * j.val)) (pieces j).toPoly)
    (by simpa only [CPolynomial.natDegree_toPoly] using hpieces j)
  omega

/-- The two-coefficient linear mask also fits the fixed 2048-element IPA vector. -/
theorem linearMaskPolynomial_natDegree_lt (coefficients : Fp × Fp) :
    (linearMaskPolynomial coefficients).natDegree < 2048 := by
  rw [linearMaskPolynomial, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_add,
    CPolynomial.toPoly_mul, CPolynomial.C_toPoly, CPolynomial.C_toPoly, CPolynomial.X_toPoly]
  apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ ?_)
  · simp
  · exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) (by simp)

/-- Every member of every exact opening group satisfies the required degree bound. -/
theorem plonkOpeningGroups_natDegree_lt {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x : Fp) (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp)
    (hdegree : PlonkDegreeBounds pub pieces) (i : Fin 5)
    (poly : CPoly) (hpoly : poly ∈ plonkOpeningGroups pub rows x pieces coefficients i) :
    poly.natDegree < 2048 := by
  have hprefix : ∀ p ∈ plonkFirstGroupPrefix pub rows x pieces, p.natDegree < 2048 := by
    intro p hp
    simp only [plonkFirstGroupPrefix, List.append_assoc, List.mem_append, List.mem_flatMap,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hp
    rcases hp with ⟨a, _, ha⟩ | ⟨j, _, rfl⟩ | ⟨j, _, rfl⟩ | rfl
    · rcases ha with rfl | ⟨l, _, rfl⟩
      · exact hdegree.instances a
      · exact privateColumnPolynomial_natDegree_lt rows (.lookupTable a l)
    · exact hdegree.fixed (plonkFixedQueryOrder j)
    · exact hdegree.sigma j
    · exact plonkCollapsedQuotient_natDegree_lt x pieces hdegree.quotient
  induction i using Fin.cases with
  | zero =>
    simp only [plonkOpeningGroups, Fin.cons_zero, List.mem_append, List.mem_singleton] at hpoly
    rcases hpoly with hp | rfl
    · exact hprefix poly hp
    · exact linearMaskPolynomial_natDegree_lt coefficients
  | succ i =>
    simp only [plonkOpeningGroups, Fin.cons_succ, List.mem_map] at hpoly
    obtain ⟨id, _, rfl⟩ := hpoly
    exact privateColumnPolynomial_natDegree_lt rows id

/-- Collapsing each group preserves its members' strict degree bound. -/
theorem plonkOpeningPolynomials_natDegree_lt {actions : ℕ} (pub : PlonkPublicPolynomials actions)
    (rows : ColumnHistory 2048) (x x1 : Fp) (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp)
    (hdegree : PlonkDegreeBounds pub pieces) (i : Fin 5) :
    (plonkOpeningPolynomials pub rows x x1 pieces coefficients i).natDegree < 2048 :=
  plonkPolynomialFold_natDegree_lt (by decide) x1 _
    (plonkOpeningGroups_natDegree_lt pub rows x pieces coefficients hdegree i)

section IpaInput

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Derive the valid-opening premises for the IPA from the pinned five-group computation. -/
theorem plonkMultiopenIpa_validOpening {actions : ℕ} (urs : URS G) (hk : urs.k = 11)
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp) (blinds : PlonkCommitmentBlinds actions)
    (hpoints : Function.Injective (plonkObservationPoints (omegaOf 11) x q))
    (hdegree : PlonkDegreeBounds pub pieces) :
    let groups := plonkBlindedOpeningGroups pub rows x x1 pieces coefficients blinds
    let ipa := computedMultiopenIpaPublic urs x2 x4 q xi z blinds.quotientPrime rounds groups
    let vector := polynomialCoefficients (2 ^ urs.k) (multiopenFinalPolynomial x2 x4 groups)
    ipa.commitment = commitGen ipa.generators vector + multiopenFinalBlind x4 blinds.quotientPrime groups • ipa.W ∧
      coefficientEvaluation urs.k ipa.point vector = ipa.value := by
  apply computedMultiopenIpaPublic_validOpening
  all_goals
    intro group hgroup
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hgroup
  · exact plonkOpeningPointSets_nodup (omegaOf 11) x q hpoints i
  · exact plonkOpeningPointSets_away (omegaOf 11) x q hpoints i
  · exact (plonkOpeningPointSets_length (omegaOf 11) x i).1
  · exact (plonkOpeningPointSets_length (omegaOf 11) x i).2.trans (by rw [hk]; decide)
  · simpa only [hk] using plonkOpeningPolynomials_natDegree_lt pub rows x x1 pieces coefficients hdegree i

end IpaInput

section Simulation

variable {G : Type*} [AddCommGroup G] [Module Fp G] [Fintype G]

/-- Exact IPA simulation after the computed five-group opening, for ideal IPA coins.

The polynomial, blind, and evaluation premises are derived above. The simulator still
starts from the resulting public IPA opening; this is not yet joint pre-IPA simulation. -/
theorem idealPlonkMultiopenIpa_simulation {actions : ℕ} (urs : URS G) (hk : urs.k = 11)
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp) (blinds : PlonkCommitmentBlinds actions)
    (hpoints : Function.Injective (plonkObservationPoints (omegaOf 11) x q))
    (hdegree : PlonkDegreeBounds pub pieces)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) (hxi : xi ≠ 0)
    (hu : ∀ j, rounds j ≠ 0) :
    let groups := plonkBlindedOpeningGroups pub rows x x1 pieces coefficients blinds
    let ipa := computedMultiopenIpaPublic urs x2 x4 q xi z blinds.quotientPrime rounds groups
    let vector := polynomialCoefficients (2 ^ urs.k) (multiopenFinalPolynomial x2 x4 groups)
    idealIpaProver ipa vector (multiopenFinalBlind x4 blinds.quotientPrime groups) =
      idealIpaSimulator ipa := by
  have h := plonkMultiopenIpa_validOpening urs hk pub rows x x1 x2 x4 q xi z rounds
    pieces coefficients blinds hpoints hdegree
  exact idealIpa_simulation_capstone _ _ _ hW hxi h.1 h.2 hu

/-- The wide-reduced IPA coins cost `34 × bias` after the same computed opening.

No distribution or independence premise is placed on the inherited blind: this statement
holds for each preceding private state. Combining those states with the public pre-IPA
view remains a separate distribution-composition step. -/
theorem sampledPlonkMultiopenIpa_simulation {actions : ℕ} (urs : URS G) (hk : urs.k = 11)
    (pub : PlonkPublicPolynomials actions) (rows : ColumnHistory 2048)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : Fin 8 → CPoly) (coefficients : Fp × Fp) (blinds : PlonkCommitmentBlinds actions)
    (hpoints : Function.Injective (plonkObservationPoints (omegaOf 11) x q))
    (hdegree : PlonkDegreeBounds pub pieces)
    (hW : Function.Bijective (fun r : Fp => r • urs.w)) (hxi : xi ≠ 0)
    (hu : ∀ j, rounds j ≠ 0) :
    let groups := plonkBlindedOpeningGroups pub rows x x1 pieces coefficients blinds
    let ipa := computedMultiopenIpaPublic urs x2 x4 q xi z blinds.quotientPrime rounds groups
    let vector := polynomialCoefficients (2 ^ urs.k) (multiopenFinalPolynomial x2 x4 groups)
    PMFEventBiasLE (sampledIpaProver ipa vector (multiopenFinalBlind x4 blinds.quotientPrime groups))
        (idealIpaSimulator ipa) (34 * challenge255Bias) ∧
      PMFEventBiasLE (idealIpaSimulator ipa)
        (sampledIpaProver ipa vector (multiopenFinalBlind x4 blinds.quotientPrime groups))
        (34 * challenge255Bias) := by
  have h := plonkMultiopenIpa_validOpening urs hk pub rows x x1 x2 x4 q xi z rounds
    pieces coefficients blinds hpoints hdegree
  have hsim := sampledIpa_simulation_error_bound
    (computedMultiopenIpaPublic urs x2 x4 q xi z blinds.quotientPrime rounds
      (plonkBlindedOpeningGroups pub rows x x1 pieces coefficients blinds))
    _ _ hW hxi h.1 h.2 hu
  norm_num only [hk, Nat.cast_ofNat] at hsim
  exact hsim

end Simulation

end Zcash.Snark.ZeroKnowledge
