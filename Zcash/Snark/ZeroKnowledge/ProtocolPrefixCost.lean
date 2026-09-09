import Zcash.Snark.ZeroKnowledge.ProtocolCausality
import Zcash.Snark.ZeroKnowledge.TranscriptAbsorbCost

/-! # Counted construction of the original pre-challenge prefix -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Copy exactly the messages due before the selected receive, counting every visited cell. -/
def protocolPrefixCosted {F G : Type*} :
    ℕ → List (TranscriptElt F G) → List (TranscriptElt F G) × ℕ
  | _, [] => ([], 1)
  | 0, .challenge :: _ => ([], 2)
  | count + 1, .challenge :: rest =>
    let tail := protocolPrefixCosted count rest
    (.challenge :: tail.1, tail.2 + 4)
  | count, .point point :: rest =>
    let tail := protocolPrefixCosted count rest
    (.point point :: tail.1, tail.2 + 3)
  | count, .scalar scalar :: rest =>
    let tail := protocolPrefixCosted count rest
    (.scalar scalar :: tail.1, tail.2 + 3)

/-- Prefix construction agrees at every receive index, including beyond the final marker. -/
theorem protocolPrefixCosted_result {F G : Type*} (count : ℕ) (trace : List (TranscriptElt F G)) :
    (protocolPrefixCosted count trace).1 = protocolPrefix count trace := by
  induction trace generalizing count with
  | nil => rfl
  | cons item rest ih =>
    cases item with
    | point point => simp only [protocolPrefixCosted, protocolPrefix, ih]
    | scalar scalar => simp only [protocolPrefixCosted, protocolPrefix, ih]
    | challenge => cases count <;> simp only [protocolPrefixCosted, protocolPrefix, ih]

/-- The constructed prefix contains no more items than its source trace. -/
theorem protocolPrefixCosted_length_le {F G : Type*} (count : ℕ) (trace : List (TranscriptElt F G)) :
    (protocolPrefixCosted count trace).1.length ≤ trace.length := by
  rw [protocolPrefixCosted_result]
  exact (protocolPrefix_isPrefix count trace).length_le

/-- Prefix construction has a linear bound even when every marker is passed. -/
theorem protocolPrefixCosted_cost_le {F G : Type*} (count : ℕ) (trace : List (TranscriptElt F G)) :
    (protocolPrefixCosted count trace).2 ≤ 4 * trace.length + 2 := by
  induction trace generalizing count with
  | nil => simp [protocolPrefixCosted]
  | cons item rest ih =>
    cases item with
    | point point =>
      have h := ih count
      simp only [protocolPrefixCosted, List.length_cons]
      omega
    | scalar scalar =>
      have h := ih count
      simp only [protocolPrefixCosted, List.length_cons]
      omega
    | challenge =>
      cases count with
      | zero => simp [protocolPrefixCosted]
      | succ count =>
        have h := ih count
        simp only [protocolPrefixCosted, List.length_cons]
        omega

end Zcash.Snark.ZeroKnowledge
