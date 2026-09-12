import Zcash.Snark.ZeroKnowledge.StreamTestProgram
import Zcash.Snark.ZeroKnowledge.RawTapeTestProgram

namespace Zcash.Snark.ZeroKnowledge
set_option exponentiation.threshold 1024

/-- A present programming-failure record is not confused with the absent suffix of a stopped stream. -/
theorem recordedTest_history_absence_regression :
    recordedViewTest ⟨[.input (.historyPresent 0)], 0⟩ [] (⟨[(none, [])], false⟩, []) = true ∧
    recordedViewTest ⟨[.input (.outputPresent 0)], 0⟩ [] (⟨[(none, [])], false⟩, []) = false ∧
    recordedViewTest ⟨[.input (.historyPresent 1)], 0⟩ [] (⟨[(none, [])], false⟩, []) = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Intermediate cache selection does not silently read the final cache. -/
theorem recordedTest_cache_routing_regression :
    let view : ActionRetryRecordedView := (⟨[(none, [])], false⟩, [(([], []), 0)])
    recordedViewTest ⟨[.input (.cachePresent (some 0) 0)], 0⟩ [] view = false ∧
    recordedViewTest ⟨[.input (.cachePresent none 0)], 0⟩ [] view = true := by
  exact ⟨rfl, rfl⟩

/-- Query personalization and query payload are separate observable byte strings. -/
theorem recordedTest_query_parts_regression :
    let view : ActionRetryRecordedView := (⟨[], false⟩, [(([1], [0]), 0)])
    recordedViewTest ⟨[.input (.cacheByte none 0 false 0 (some ⟨0, by decide⟩))], 0⟩ [] view = true ∧
    recordedViewTest ⟨[.input (.cacheByte none 0 true 0 (some ⟨0, by decide⟩))], 0⟩ [] view = false := by
  exact ⟨rfl, rfl⟩

/-- The ordinary raw-prefix circuit actually depends on candidate bits, including a zero-valued present word. -/
theorem rawTapeTest_candidate_regression :
    rawTapeTest ⟨[.input (.word 0 0 (some ⟨0, by decide⟩))], 0⟩ [] [[1]] = true ∧
    rawTapeTest ⟨[.input (.word 0 0 (some ⟨0, by decide⟩))], 0⟩ [] [[0]] = false ∧
    rawTapeTest ⟨[.input (.word 0 0 none)], 0⟩ [] [[0]] = true ∧
    rawTapeTest ⟨[.input (.word 0 0 none)], 0⟩ [] [[]] = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Shared wires retain their order through several gates; an out-of-range wire has the declared false default. -/
theorem booleanTest_wire_routing_regression :
    (BooleanTestProgram.eval (Input := Unit) ⟨[.constant true, .constant false, .nand 1 1, .nand 0 0], 0⟩ (fun _ => false)) = true ∧
    (BooleanTestProgram.eval (Input := Unit) ⟨[.constant true], 4⟩ (fun _ => true)) = false := by
  exact ⟨rfl, rfl⟩

/-- Recorded observations distinguish identity failures from duplicate opening errors. -/
theorem recordedTest_failure_status_regression :
    let view : ActionRetryRecordedView := (⟨[(some ⟨[], [], .failed .coincidentOpeningQueries⟩, [])], false⟩, [])
    recordedViewTest ⟨[.input (.status 0 (.failed .identityPoint))], 0⟩ [] view = false ∧
    recordedViewTest ⟨[.input (.status 0 (.failed .coincidentOpeningQueries))], 0⟩ [] view = true := by
  exact ⟨rfl, rfl⟩

end Zcash.Snark.ZeroKnowledge
