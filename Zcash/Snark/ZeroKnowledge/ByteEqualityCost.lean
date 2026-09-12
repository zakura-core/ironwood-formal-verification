import Zcash.Snark.ZeroKnowledge.ByteFiatShamir

/-!
# Structural execution costs for byte-oracle address equality

Inputs are materialized finite byte lists. The cost model charges one unit for a
pair-of-list case test, one for a fixed-width byte comparison, and one for the
branch between domain and payload comparison. Both algorithms retain their
counters when a comparison stops early. These primitives are the equality layer
used by the costed cache execution, with exact erasure to the existing equality.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- Compare byte lists and count pair-of-list case tests and byte comparisons. -/
def byteListEqCosted : List UInt8 → List UInt8 → Bool × ℕ
  | [], [] => (true, 1)
  | [], _ :: _ | _ :: _, [] => (false, 1)
  | left :: restLeft, right :: restRight =>
    if left = right then
      let next := byteListEqCosted restLeft restRight
      (next.1, next.2 + 2)
    else (false, 2)

/-- Forgetting the byte comparator's counter gives the original equality test. -/
theorem byteListEqCosted_result (left right : List UInt8) :
    (byteListEqCosted left right).1 = decide (left = right) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons head rest ih =>
    cases right with
    | nil => rfl
    | cons other tail =>
      by_cases heq : head = other <;> simp [byteListEqCosted, heq, ih]

/-- The cost depends on the queried prefix length even when the stored address is longer. -/
theorem byteListEqCosted_cost_le (left right : List UInt8) :
    (byteListEqCosted left right).2 ≤ 2 * left.length + 1 := by
  induction left generalizing right with
  | nil => cases right <;> simp [byteListEqCosted]
  | cons head rest ih =>
    cases right with
    | nil => simp [byteListEqCosted]
    | cons other tail =>
      by_cases heq : head = other
      · have h := ih tail
        simp only [byteListEqCosted, if_pos heq, List.length_cons]
        omega
      · simp only [byteListEqCosted, if_neg heq, List.length_cons]
        omega

/-- Compare the personalization and payload of the actual byte-oracle address. -/
def transcriptAddressEqCosted (left right : TranscriptHashAddress) : Bool × ℕ :=
  let domain := byteListEqCosted left.1 right.1
  if domain.1 then
    let payload := byteListEqCosted left.2 right.2
    (payload.1, domain.2 + payload.2 + 1)
  else (false, domain.2 + 1)

/-- Cost erasure preserves the actual pair-of-byte-lists equality used by the cache. -/
theorem transcriptAddressEqCosted_result (left right : TranscriptHashAddress) :
    (transcriptAddressEqCosted left right).1 = decide (left = right) := by
  unfold transcriptAddressEqCosted
  simp only [byteListEqCosted_result]
  by_cases h : left.1 = right.1
  · simp [h, Prod.ext_iff]
  · simp [h, Prod.ext_iff]

/-- Comparing one address costs at most twice its byte length plus three case or branch tests. -/
theorem transcriptAddressEqCosted_cost_le (left right : TranscriptHashAddress) :
    (transcriptAddressEqCosted left right).2 ≤ 2 * (left.1.length + left.2.length) + 3 := by
  have hd := byteListEqCosted_cost_le left.1 right.1
  have hp := byteListEqCosted_cost_le left.2 right.2
  unfold transcriptAddressEqCosted
  dsimp only
  split <;> dsimp only <;> omega

end Zcash.Snark.ZeroKnowledge
