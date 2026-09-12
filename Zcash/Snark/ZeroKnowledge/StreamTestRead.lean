import Zcash.Snark.ZeroKnowledge.RecordedTestRead

namespace Zcash.Snark.ZeroKnowledge
open MeasureTheory

/-- A stream test observes particular attempts and their returned caches, and stored auxiliary words. -/
inductive StreamTestAddress
  | historyPresent (attempt : ℕ)
  | outputPresent (attempt : ℕ)
  | status (attempt : ℕ) (expected : ProverAttemptStatus)
  | proof (attempt byte : ℕ) (bit : Option (Fin 8))
  | scalar (attempt column : ℕ) (bit : Option (Fin 255))
  | cachePresent (attempt entry : ℕ)
  | cacheByte (attempt entry : ℕ) (second : Bool) (byte : ℕ) (bit : Option (Fin 8))
  | cacheReply (attempt entry : ℕ) (bit : Fin 512)
  | auxiliary (word : ℕ) (bit : Option (Fin 512))

/-- The same public address in a finite recorded history; no global final-state guess is made. -/
def StreamTestAddress.toRecorded : StreamTestAddress → RecordedTestAddress
  | .historyPresent i => .historyPresent i
  | .outputPresent i => .outputPresent i
  | .status i expected => .status i expected
  | .proof i byte bit => .proof i byte bit
  | .scalar i column bit => .scalar i column bit
  | .cachePresent i entry => .cachePresent (some i) entry
  | .cacheByte i entry second byte bit => .cacheByte (some i) entry second byte bit
  | .cacheReply i entry bit => .cacheReply (some i) entry bit
  | .auxiliary word bit => .auxiliary word bit

def StreamTestAddress.index : StreamTestAddress → ℕ
  | .historyPresent i | .outputPresent i | .status i _ | .proof i _ _ | .scalar i _ _ => i
  | .cachePresent i _ | .cacheByte i _ _ _ _ | .cacheReply i _ _ => i
  | .auxiliary _ _ => 0

/-- A port depends on at most one stream entry; auxiliary ports ignore that entry. -/
def StreamTestAddress.readEntry (address : StreamTestAddress) (auxiliary : List (Fin challengeDigestCard))
    (entry : ActionRetryStreamEntry) : Bool :=
  match address with
  | .historyPresent _ => entry.isSome
  | .outputPresent _ => (entry.bind Prod.fst).isSome
  | .status _ expected => ((entry.bind Prod.fst).map (fun attempt => decide (attempt.status = expected))).getD false
  | .proof _ byte bit => optionalByteTest ((entry.bind Prod.fst).getD testEmptyAttempt).proof[byte]? bit
  | .scalar _ column bit => optionalFieldTest ((entry.bind Prod.fst).getD testEmptyAttempt).received[column]? bit
  | .cachePresent _ offset => (entry.getD (none, [])).2[offset]?.isSome
  | .cacheByte _ offset second byte bit =>
    let query := (((entry.getD (none, [])).2[offset]?).map Prod.fst).getD ([], [])
    optionalByteTest (if second then query.2 else query.1)[byte]? bit
  | .cacheReply _ offset bit => optionalRawWordTest (((entry.getD (none, [])).2[offset]?).map Prod.snd) (some bit)
  | .auxiliary word bit => optionalRawWordTest auxiliary[word]? bit

def StreamTestAddress.eval (address : StreamTestAddress) (auxiliary : List (Fin challengeDigestCard))
    (stream : ℕ → ActionRetryStreamEntry) : Bool := address.readEntry auxiliary (stream address.index)

/-- Each port is measurable in the original complete-stream probability space. -/
theorem StreamTestAddress.eval_measurable (address : StreamTestAddress) (auxiliary : List (Fin challengeDigestCard)) :
    Measurable (address.eval auxiliary) :=
  (Measurable.of_discrete : Measurable (address.readEntry auxiliary)).comp (measurable_pi_apply address.index)

/-- Every finite recorded view is read exactly as its corresponding stopped-or-truncated stream. -/
theorem StreamTestAddress.eval_recorded (address : StreamTestAddress) (auxiliary : List (Fin challengeDigestCard))
    (view : ActionRetryRecordedView) :
    address.eval auxiliary (fun index => view.1.attempts[index]?) = address.toRecorded.eval auxiliary view := by
  cases address <;>
    simp only [eval, readEntry, index, toRecorded, RecordedTestAddress.eval, recordedTestOutput, recordedTestCache,
      List.getD_eq_getElem?_getD]

end Zcash.Snark.ZeroKnowledge
