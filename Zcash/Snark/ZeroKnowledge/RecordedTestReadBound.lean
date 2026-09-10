import Zcash.Snark.ZeroKnowledge.RecordedTestRead

namespace Zcash.Snark.ZeroKnowledge

/-- Reading an attempt history entry has cost linear in its index, supplying the first stage of
recorded-view access. -/
theorem recordedTestHistoryCosted_cost_le (read : ℕ) (view : ActionRetryRecordedView) (index : ℕ) :
    (recordedTestHistoryCosted read view index).2 ≤ 2 * index + read + 4 := by
  have h := getOptionListCosted_cost_le read view.1.attempts index
  dsimp only [recordedTestHistoryCosted]
  omega

/-- Reading an attempt output includes history traversal and projection, supplying the output-reader
budget. -/
theorem recordedTestOutputCosted_cost_le (read : ℕ) (view : ActionRetryRecordedView) (index : ℕ) :
    (recordedTestOutputCosted read view index).2 ≤ 2 * index + read + 7 := by
  have h := recordedTestHistoryCosted_cost_le read view index
  dsimp only [recordedTestOutputCosted]
  omega

/-- Selecting the initial or retained cache fits the slot-traversal budget, accounting for
cache-history access. -/
theorem recordedTestCacheCosted_cost_le (read : ℕ) (view : ActionRetryRecordedView) (slot : RecordedTestCacheSlot) :
    (recordedTestCacheCosted read view slot).2 ≤ 2 * slot.getD 0 + read + 4 := by
  cases slot with
  | none => simp only [recordedTestCacheCosted, Option.getD_none]; omega
  | some index =>
    have h := getDListCosted_cost_le_index read (none, []) view.1.attempts index
    dsimp only [recordedTestCacheCosted, Option.getD_some]
    omega

/-- A recorded proof-byte read charges both attempt and byte traversal, supplying the Boolean test's
proof-reader bound. -/
theorem recordedTestProofCosted_cost_le (read : ℕ) (view : ActionRetryRecordedView) (index byte : ℕ) :
    (recordedTestProofCosted read view index byte).2 ≤ 2 * index + 2 * byte + 2 * read + 11 := by
  have ha := recordedTestOutputCosted_cost_le read view index
  have hb := getOptionListCosted_cost_le read
    ((recordedTestOutputCosted read view index).1.getD testEmptyAttempt).proof byte
  dsimp only [recordedTestProofCosted]
  omega

/-- A recorded scalar read charges both attempt and scalar traversal, supplying the scalar-reader
bound. -/
theorem recordedTestScalarCosted_cost_le (read : ℕ) (view : ActionRetryRecordedView) (index scalar : ℕ) :
    (recordedTestScalarCosted read view index scalar).2 ≤ 2 * index + 2 * scalar + 2 * read + 11 := by
  have ha := recordedTestOutputCosted_cost_le read view index
  have hb := getOptionListCosted_cost_le read
    ((recordedTestOutputCosted read view index).1.getD testEmptyAttempt).received scalar
  dsimp only [recordedTestScalarCosted]
  omega

/-- A cache-entry read charges cache selection and entry traversal, supplying the nested reader
bound. -/
theorem recordedTestCacheEntryCosted_cost_le (read : ℕ) (view : ActionRetryRecordedView)
    (slot : RecordedTestCacheSlot) (entry : ℕ) :
    (recordedTestCacheEntryCosted read view slot entry).2 ≤ 2 * slot.getD 0 + 2 * entry + 2 * read + 8 := by
  have hc := recordedTestCacheCosted_cost_le read view slot
  have he := getOptionListCosted_cost_le read (recordedTestCacheCosted read view slot).1 entry
  dsimp only [recordedTestCacheEntryCosted]
  omega

/-- A cache-address byte read charges cache, entry, and byte traversal, completing the recorded-view
input budget. -/
theorem recordedTestCacheByteCosted_cost_le (read : ℕ) (view : ActionRetryRecordedView)
    (slot : RecordedTestCacheSlot) (entry : ℕ) (second : Bool) (byte : ℕ) :
    (recordedTestCacheByteCosted read view slot entry second byte).2 ≤
      2 * slot.getD 0 + 2 * entry + 2 * byte + 3 * read + 14 := by
  have he := recordedTestCacheEntryCosted_cost_le read view slot entry
  let query := ((recordedTestCacheEntryCosted read view slot entry).1.map Prod.fst).getD ([], [])
  have hb := getOptionListCosted_cost_le read (if second then query.2 else query.1) byte
  dsimp only [query] at hb
  dsimp only [recordedTestCacheByteCosted]
  omega

/-- A structural address size bounds every traversed public list; it includes auxiliary-data addresses. -/
def RecordedTestAddress.indexSum : RecordedTestAddress → ℕ
  | .exhausted => 0
  | .historyPresent index | .outputPresent index | .status index _ => index
  | .proof index byte _ => index + byte
  | .scalar index column _ => index + column
  | .cachePresent slot entry | .cacheReply slot entry _ => slot.getD 0 + entry
  | .cacheByte slot entry _ byte _ => slot.getD 0 + entry + byte
  | .auxiliary index _ => index

/-- The same explicit price bounds all values, failed attempts, and arbitrarily large retained caches. -/
def RecordedTestAddress.costBudget (address : RecordedTestAddress) (read canonicalRead : ℕ) : ℕ :=
  2 * address.indexSum + 3 * read + canonicalRead + 32

/-- All public-view and retained-auxiliary reader costs are discharged for this concrete instruction set. -/
theorem RecordedTestAddress.evalCosted_cost_le (address : RecordedTestAddress) (read canonicalRead : ℕ)
    (auxiliary : List (Fin challengeDigestCard)) (view : ActionRetryRecordedView) :
    (address.evalCosted read canonicalRead auxiliary view).2 ≤ address.costBudget read canonicalRead := by
  cases address with
  | exhausted => dsimp only [evalCosted, costBudget, indexSum]; omega
  | historyPresent index =>
    have h := recordedTestHistoryCosted_cost_le read view index
    dsimp only [evalCosted, costBudget, indexSum]
    omega
  | outputPresent index =>
    have h := recordedTestOutputCosted_cost_le read view index
    dsimp only [evalCosted, costBudget, indexSum]
    omega
  | status index status =>
    have h := recordedTestOutputCosted_cost_le read view index
    dsimp only [evalCosted, costBudget, indexSum]
    omega
  | proof index byte bit =>
    have h := recordedTestProofCosted_cost_le read view index byte
    dsimp only [evalCosted, costBudget, indexSum]
    omega
  | scalar index scalar bit =>
    have h := recordedTestScalarCosted_cost_le read view index scalar
    dsimp only [evalCosted, costBudget, indexSum]
    omega
  | cachePresent slot entry =>
    have h := recordedTestCacheEntryCosted_cost_le read view slot entry
    dsimp only [evalCosted, costBudget, indexSum]
    omega
  | cacheByte slot entry second byte bit =>
    have h := recordedTestCacheByteCosted_cost_le read view slot entry second byte
    dsimp only [evalCosted, costBudget, indexSum]
    omega
  | cacheReply slot entry bit =>
    have h := recordedTestCacheEntryCosted_cost_le read view slot entry
    dsimp only [evalCosted, costBudget, indexSum]
    omega
  | auxiliary index bit =>
    have h := getOptionListCosted_cost_le read auxiliary index
    dsimp only [evalCosted, costBudget, indexSum]
    omega

end Zcash.Snark.ZeroKnowledge
