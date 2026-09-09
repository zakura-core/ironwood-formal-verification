import Zcash.Snark.ZeroKnowledge.PlonkStoredTapeBound

/-!
# Exact stored challenge prices, independent of random values

Every scheduled challenge index is in the generated field list. Its traversal
cost therefore depends only on that index and the primitive read price. These
equalities remove the random tape's values from the complete runtime budget.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- An in-range stored-list lookup has its exact index-dependent cost. -/
theorem getDListCosted_cost_of_lt {α : Type*} (read : ℕ) (fallback : α)
    (values : List α) (index : ℕ) (hindex : index < values.length) :
    (getDListCosted read fallback values index).2 = 2 * index + read + 1 := by
  induction values generalizing index with
  | nil => simp at hindex
  | cons first rest ih =>
    cases index with
    | zero => simp [getDListCosted]
    | succ index =>
      have hi : index < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hindex
      simp only [getDListCosted, ih index hi]
      omega

/-- The fixed routing charge adds ten units to the exact in-range traversal cost. -/
theorem storedPlonkFieldReadCosted_cost_of_lt (read : ℕ) (fields : List Fp) (base slot : ℕ)
    (hindex : base + slot < fields.length) :
    (storedPlonkFieldReadCosted read fields base slot).2 = 2 * (base + slot) + read + 11 := by
  simp only [storedPlonkFieldReadCosted, getDListCosted_cost_of_lt read 0 fields (base + slot) hindex]

/-- Project exactly the access prices of all prepared verifier challenges. -/
def Challenges.readPrices {k : ℕ} {F : Type*} (ch : Challenges k (F × ℕ)) : Challenges k ℕ where
  theta := ch.theta.2
  beta := ch.beta.2
  gamma := ch.gamma.2
  y := ch.y.2
  x := ch.x.2
  x1 := ch.x1.2
  x2 := ch.x2.2
  x3 := ch.x3.2
  x4 := ch.x4.2
  xi := ch.xi.2
  z := ch.z.2
  ipaRound := fun index => (ch.ipaRound index).2

/-- A zero-valued record naming the original challenge positions' exact read prices. -/
def storedPlonkChallengePriceModel (k read : ℕ) : Challenges k (Fp × ℕ) :=
  plonkChallengesFromTape (fun index => (0, 2 * index.val + read + 11))

/-- The generated challenge record has those same prices for every possible bit-list value. -/
theorem storedPlonkSimulatorTapesCosted_challenge_prices (actions k read : ℕ) (bits : List Bool) :
    Challenges.readPrices (storedPlonkSimulatorTapesCosted actions k read bits).1.challenges =
      Challenges.readPrices (storedPlonkChallengePriceModel k read) := by
  let fields := storedFieldTapeCosted ((k + 11) + plonkSimulatorSampleCount actions k) read bits
  have hlength : fields.1.length = (k + 11) + plonkSimulatorSampleCount actions k := ofFnCosted_length _
  have hprice (index : Fin (k + 11)) :
      (storedPlonkFieldReadCosted read fields.1 0 index.val).2 = 2 * index.val + read + 11 := by
    have hi : 0 + index.val < fields.1.length := by rw [hlength]; have h := index.isLt; omega
    simpa only [Nat.zero_add] using storedPlonkFieldReadCosted_cost_of_lt read fields.1 0 index.val hi
  change plonkChallengesFromTape (k := k)
    (fun index => (storedPlonkFieldReadCosted read fields.1 0 index.val).2) =
      plonkChallengesFromTape (fun index => 2 * index.val + read + 11)
  exact congrArg (plonkChallengesFromTape (k := k)) (funext hprice)

end Zcash.Snark.ZeroKnowledge
