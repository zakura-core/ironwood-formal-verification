import Zcash.Snark.ZeroKnowledge.ListRoutingCost

namespace Zcash.Snark.ZeroKnowledge

/-- Count every traversed list cell when determining a stored input's length. -/
def lengthListCosted {A : Type*} : List A → ℕ × ℕ
  | [] => (0, 1)
  | _ :: rest =>
    let tail := lengthListCosted rest
    (tail.1 + 1, tail.2 + 1)

/-- The counted traversal returns exactly the original length. -/
theorem lengthListCosted_result {A : Type*} (values : List A) :
    (lengthListCosted values).1 = values.length := by
  induction values <;> simp_all [lengthListCosted]

/-- Exact length-traversal cost. -/
theorem lengthListCosted_cost {A : Type*} (values : List A) :
    (lengthListCosted values).2 = values.length + 1 := by
  induction values <;> simp_all [lengthListCosted, Nat.add_assoc]

/-- Reverse into an accumulator while charging every copied cell. -/
def reverseAuxListCosted {A : Type*} : List A → List A → List A × ℕ
  | [], accumulator => (accumulator, 1)
  | value :: rest, accumulator =>
    let tail := reverseAuxListCosted rest (value :: accumulator)
    (tail.1, tail.2 + 2)

/-- The accumulator program has exactly the original reverse-append result. -/
theorem reverseAuxListCosted_result {A : Type*} (values accumulator : List A) :
    (reverseAuxListCosted values accumulator).1 = values.reverse ++ accumulator := by
  induction values generalizing accumulator with
  | nil => simp [reverseAuxListCosted]
  | cons value rest ih => simp [reverseAuxListCosted, ih, List.append_assoc]

/-- Exact reverse cost, including the terminal accumulator return. -/
theorem reverseAuxListCosted_cost {A : Type*} (values accumulator : List A) :
    (reverseAuxListCosted values accumulator).2 = 2 * values.length + 1 := by
  induction values generalizing accumulator with
  | nil => simp [reverseAuxListCosted]
  | cons value rest ih => simp [reverseAuxListCosted, ih, Nat.mul_add]

/-- Materialize the complete reversed list. -/
def reverseListCosted {A : Type*} (values : List A) : List A × ℕ :=
  reverseAuxListCosted values []

/-- Reverse erasure preserves the original ordering. -/
theorem reverseListCosted_result {A : Type*} (values : List A) :
    (reverseListCosted values).1 = values.reverse := by
  simp [reverseListCosted, reverseAuxListCosted_result]

/-- Exact cost of reversing a materialized list. -/
theorem reverseListCosted_cost {A : Type*} (values : List A) :
    (reverseListCosted values).2 = 2 * values.length + 1 :=
  reverseAuxListCosted_cost values []

end Zcash.Snark.ZeroKnowledge
