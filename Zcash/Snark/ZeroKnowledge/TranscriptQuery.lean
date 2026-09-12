import Zcash.Snark.ZeroKnowledge.ByteFiatShamir
import Zcash.Snark.ZeroKnowledge.ProtocolCausality

/-!
# Distinct hash addresses at successive challenge boundaries

The next query absorbs the messages already due, followed by one challenge
marker. Counting markers distinguishes every scheduled query. The lossless
byte encoding carries that distinction to the raw-hash addresses.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The full typed absorb prefix immediately before receiving challenge `index`. -/
def protocolQueryPrefix {F G : Type*} (initial trace : List (TranscriptElt F G)) (index : ℕ) :
    List (TranscriptElt F G) := initial ++ protocolPrefix index trace ++ [.challenge]

/-- Each successive query prefix has exactly one more challenge marker. -/
theorem protocolQueryPrefix_challengeCount {F G : Type*}
    (initial trace : List (TranscriptElt F G)) (index : ℕ) :
    protocolChallengeCount (protocolQueryPrefix initial trace index) =
      protocolChallengeCount initial + min index (protocolChallengeCount trace) + 1 := by
  simp only [protocolQueryPrefix, protocolChallengeCount_append, protocolPrefix_challengeCount,
    protocolChallengeCount, Nat.add_zero]

/-- Distinct scheduled receive positions give distinct typed query prefixes. -/
theorem protocolQueryPrefix_inj {F G : Type*} (initial trace : List (TranscriptElt F G))
    (left right : ℕ) (hleft : left ≤ protocolChallengeCount trace)
    (hright : right ≤ protocolChallengeCount trace)
    (heq : protocolQueryPrefix initial trace left = protocolQueryPrefix initial trace right) : left = right := by
  have h := congrArg protocolChallengeCount heq
  rw [protocolQueryPrefix_challengeCount, protocolQueryPrefix_challengeCount,
    min_eq_left hleft, min_eq_left hright] at h
  omega

/-- The byte-level address for the next raw challenge digest. -/
def protocolQueryAddress (initial trace : List (TranscriptElt Fp VestaG)) (index : ℕ) :
    TranscriptHashAddress := transcriptHashAddress (protocolQueryPrefix initial trace index)

/-- Injective serialization preserves the distinction between all scheduled hash queries. -/
theorem protocolQueryAddress_inj (initial trace : List (TranscriptElt Fp VestaG))
    (left right : ℕ) (hleft : left ≤ protocolChallengeCount trace)
    (hright : right ≤ protocolChallengeCount trace)
    (heq : protocolQueryAddress initial trace left = protocolQueryAddress initial trace right) : left = right :=
  protocolQueryPrefix_inj initial trace left right hleft hright (transcriptHashAddress_injective heq)

/-- No interval of the scheduled query list repeats an address. -/
theorem protocolQueryAddresses_nodup (initial trace : List (TranscriptElt Fp VestaG))
    (budget index : ℕ) (hbudget : index + budget ≤ protocolChallengeCount trace) :
    ((List.range' index budget).map (protocolQueryAddress initial trace)).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range'
  intro left hleft right hright heq
  have hl := List.mem_range'_1.mp hleft
  have hr := List.mem_range'_1.mp hright
  exact protocolQueryAddress_inj initial trace left right (by omega) (by omega) heq

/-- An address contains this first private point after the fixed public initialization. -/
def HasTranscriptAnchor (initial : List (TranscriptElt Fp VestaG))
    (address : TranscriptHashAddress) (point : VestaG) : Prop :=
  ∃ rest, address = transcriptHashAddress (initial ++ .point point :: rest)

/-- Every query retains the first private point, regardless of its later suffix. -/
theorem protocolQueryAddress_anchor (initial rest : List (TranscriptElt Fp VestaG))
    (point : VestaG) (index : ℕ) :
    HasTranscriptAnchor initial (protocolQueryAddress initial (.point point :: rest) index) point := by
  refine ⟨protocolPrefix index rest ++ [.challenge], ?_⟩
  simp only [protocolQueryAddress, protocolQueryPrefix, protocolPrefix, List.append_assoc, List.cons_append]

/-- One fixed byte address can name at most one first private point. -/
theorem HasTranscriptAnchor.unique {initial : List (TranscriptElt Fp VestaG)}
    {address : TranscriptHashAddress} {left right : VestaG}
    (hleft : HasTranscriptAnchor initial address left) (hright : HasTranscriptAnchor initial address right) :
    left = right := by
  obtain ⟨leftRest, hleft⟩ := hleft
  obtain ⟨rightRest, hright⟩ := hright
  have h := transcriptHashAddress_injective (hleft.symm.trans hright)
  exact TranscriptElt.point.inj (List.cons.inj (List.append_cancel_left h)).1

end Zcash.Snark.ZeroKnowledge
