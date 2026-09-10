import Zcash.Snark.ZeroKnowledge.ActionOracleRecordedSource
import Zcash.Snark.ZeroKnowledge.IndexedTestReadCost

/-!
# Public observations available to executable distinguishing tests

The addresses expose every recorded attempt, emitted byte, received scalar,
failure status, intermediate and final cache, and a separate stored auxiliary
word list. Presence queries distinguish absence from zero-valued data. Bit
inspection is a bounded-word primitive: 8 bits for bytes, 255 for field
representatives, and 512 for raw words. Field representative access has its own
explicit price. All list traversals are implemented and charged below.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)

/-- `none` selects the final cache; `some i` selects the cache retained after attempt `i`. -/
abbrev RecordedTestCacheSlot := Option ℕ

/-- Fixed public addresses for Boolean-circuit input instructions. An absent bit index tests presence. -/
inductive RecordedTestAddress
  | exhausted
  | historyPresent (attempt : ℕ)
  | outputPresent (attempt : ℕ)
  | status (attempt : ℕ) (status : ProverAttemptStatus)
  | proof (attempt byte : ℕ) (bit : Option (Fin 8))
  | scalar (attempt scalar : ℕ) (bit : Option (Fin 255))
  | cachePresent (slot : RecordedTestCacheSlot) (entry : ℕ)
  | cacheByte (slot : RecordedTestCacheSlot) (entry : ℕ) (second : Bool) (byte : ℕ) (bit : Option (Fin 8))
  | cacheReply (slot : RecordedTestCacheSlot) (entry : ℕ) (bit : Fin 512)
  | auxiliary (word : ℕ) (bit : Option (Fin 512))

/-- Only missing outputs use this default; the public presence flag is retained separately. -/
def testEmptyAttempt : ProverAttemptResult := ⟨[], [], .complete⟩

def recordedTestOutput (view : ActionRetryRecordedView) (index : ℕ) : Option ProverAttemptResult :=
  view.1.attempts[index]?.bind Prod.fst

def recordedTestCache (view : ActionRetryRecordedView) : RecordedTestCacheSlot → ActionRetryOracleState
  | none => view.2
  | some index => (view.1.attempts.getD index (none, [])).2

def optionalByteTest (value : Option UInt8) : Option (Fin 8) → Bool
  | none => value.isSome
  | some bit => (value.map (fun byte => byte.toNat.testBit bit.val)).getD false

def optionalFieldTest (value : Option Fp) : Option (Fin 255) → Bool
  | none => value.isSome
  | some bit => (value.map (fun scalar => scalar.val.testBit bit.val)).getD false

def optionalRawWordTest (value : Option (Fin challengeDigestCard)) : Option (Fin 512) → Bool
  | none => value.isSome
  | some bit => (value.map (fun word => word.val.testBit bit.val)).getD false

/-- Source semantics of the complete public observation interface. -/
def RecordedTestAddress.eval (address : RecordedTestAddress) (auxiliary : List (Fin challengeDigestCard))
    (view : ActionRetryRecordedView) : Bool :=
  match address with
  | .exhausted => view.1.exhausted
  | .historyPresent i => view.1.attempts[i]?.isSome
  | .outputPresent i => (recordedTestOutput view i).isSome
  | .status i expected => ((recordedTestOutput view i).map (fun attempt => decide (attempt.status = expected))).getD false
  | .proof i byte bit => optionalByteTest ((recordedTestOutput view i).getD testEmptyAttempt).proof[byte]? bit
  | .scalar i column bit => optionalFieldTest ((recordedTestOutput view i).getD testEmptyAttempt).received[column]? bit
  | .cachePresent slot entry => (recordedTestCache view slot)[entry]?.isSome
  | .cacheByte slot entry second byte bit =>
    let query := (((recordedTestCache view slot)[entry]?).map Prod.fst).getD ([], [])
    optionalByteTest (if second then query.2 else query.1)[byte]? bit
  | .cacheReply slot entry bit => optionalRawWordTest (((recordedTestCache view slot)[entry]?).map Prod.snd) (some bit)
  | .auxiliary word bit => optionalRawWordTest auxiliary[word]? bit

/-- Read an attempt record, including the distinction between an absent suffix and a failed output. -/
def recordedTestHistoryCosted (read : ℕ) (view : ActionRetryRecordedView) (index : ℕ) :
    Option (Option ProverAttemptResult × ActionRetryOracleState) × ℕ :=
  let value := getOptionListCosted read view.1.attempts index
  (value.1, value.2 + 2)

def recordedTestOutputCosted (read : ℕ) (view : ActionRetryRecordedView) (index : ℕ) :
    Option ProverAttemptResult × ℕ :=
  let value := recordedTestHistoryCosted read view index
  (value.1.bind Prod.fst, value.2 + 3)

def recordedTestCacheCosted (read : ℕ) (view : ActionRetryRecordedView) :
    RecordedTestCacheSlot → ActionRetryOracleState × ℕ
  | none => (view.2, read + 2)
  | some index =>
    let value := getDListCosted read (none, []) view.1.attempts index
    (value.1.2, value.2 + 3)

def recordedTestProofCosted (read : ℕ) (view : ActionRetryRecordedView) (index byte : ℕ) : Option UInt8 × ℕ :=
  let attempt := recordedTestOutputCosted read view index
  let value := getOptionListCosted read (attempt.1.getD testEmptyAttempt).proof byte
  (value.1, attempt.2 + value.2 + 2)

def recordedTestScalarCosted (read : ℕ) (view : ActionRetryRecordedView) (index scalar : ℕ) : Option Fp × ℕ :=
  let attempt := recordedTestOutputCosted read view index
  let value := getOptionListCosted read (attempt.1.getD testEmptyAttempt).received scalar
  (value.1, attempt.2 + value.2 + 2)

def recordedTestCacheEntryCosted (read : ℕ) (view : ActionRetryRecordedView) (slot : RecordedTestCacheSlot) (entry : ℕ) :
    Option (TranscriptHashAddress × Fin challengeDigestCard) × ℕ :=
  let cache := recordedTestCacheCosted read view slot
  let value := getOptionListCosted read cache.1 entry
  (value.1, cache.2 + value.2 + 2)

def recordedTestCacheByteCosted (read : ℕ) (view : ActionRetryRecordedView) (slot : RecordedTestCacheSlot)
    (entry : ℕ) (second : Bool) (byte : ℕ) : Option UInt8 × ℕ :=
  let pair := recordedTestCacheEntryCosted read view slot entry
  let query := (pair.1.map Prod.fst).getD ([], [])
  let value := getOptionListCosted read (if second then query.2 else query.1) byte
  (value.1, pair.2 + value.2 + 4)

/-- The counted reader performs only the displayed bounded primitives and full stored-list reads. -/
def RecordedTestAddress.evalCosted (address : RecordedTestAddress) (read canonicalRead : ℕ)
    (auxiliary : List (Fin challengeDigestCard)) (view : ActionRetryRecordedView) : Bool × ℕ :=
  match address with
  | .exhausted => (view.1.exhausted, read + 2)
  | .historyPresent i => let value := recordedTestHistoryCosted read view i; (value.1.isSome, value.2 + 2)
  | .outputPresent i => let value := recordedTestOutputCosted read view i; (value.1.isSome, value.2 + 2)
  | .status i expected =>
    let value := recordedTestOutputCosted read view i
    (((value.1.map (fun attempt => decide (attempt.status = expected))).getD false), value.2 + 6)
  | .proof i byte bit => let value := recordedTestProofCosted read view i byte; (optionalByteTest value.1 bit, value.2 + 4)
  | .scalar i column bit =>
    let value := recordedTestScalarCosted read view i column
    (optionalFieldTest value.1 bit, value.2 + canonicalRead + 4)
  | .cachePresent slot entry => let value := recordedTestCacheEntryCosted read view slot entry; (value.1.isSome, value.2 + 2)
  | .cacheByte slot entry second byte bit =>
    let value := recordedTestCacheByteCosted read view slot entry second byte
    (optionalByteTest value.1 bit, value.2 + 4)
  | .cacheReply slot entry bit =>
    let value := recordedTestCacheEntryCosted read view slot entry
    (optionalRawWordTest (value.1.map Prod.snd) (some bit), value.2 + 6)
  | .auxiliary word bit => let value := getOptionListCosted read auxiliary word; (optionalRawWordTest value.1 bit, value.2 + 4)

/-- Every opcode observes the source view exactly, including absence and failure distinctions. -/
theorem RecordedTestAddress.evalCosted_result (address : RecordedTestAddress) (read canonicalRead : ℕ)
    (auxiliary : List (Fin challengeDigestCard)) (view : ActionRetryRecordedView) :
    (address.evalCosted read canonicalRead auxiliary view).1 = address.eval auxiliary view := by
  cases address <;>
    simp only [evalCosted, eval, recordedTestHistoryCosted, recordedTestOutputCosted, recordedTestProofCosted,
      recordedTestScalarCosted, recordedTestCacheEntryCosted, recordedTestCacheByteCosted,
      getOptionListCosted_result, recordedTestOutput]
  all_goals cases ‹RecordedTestCacheSlot› <;> simp only [recordedTestCacheCosted, recordedTestCache, getDListCosted_result]

end Zcash.Snark.ZeroKnowledge
