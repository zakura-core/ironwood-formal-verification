import Zcash.Snark.ZeroKnowledge.ProtocolPrefixCost
import Zcash.Snark.ZeroKnowledge.TranscriptQuery
import Zcash.Snark.ZeroKnowledge.TranscriptEncodingCost

/-! # Complete construction of the original raw-oracle query addresses -/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark
open Zcash.Arithmetic (Fp)

/-- Construct the public initialization, due messages, and next challenge marker. -/
def protocolQueryPrefixCosted {F G : Type*} (initial trace : List (TranscriptElt F G)) (index : ℕ) :
    List (TranscriptElt F G) × ℕ :=
  let due := protocolPrefixCosted index trace
  let initialized := appendProducedCosted (initial, 1) due
  appendProducedCosted initialized ([.challenge], 2)

/-- The counted query has exactly the original typed absorb prefix. -/
theorem protocolQueryPrefixCosted_result {F G : Type*}
    (initial trace : List (TranscriptElt F G)) (index : ℕ) :
    (protocolQueryPrefixCosted initial trace index).1 = protocolQueryPrefix initial trace index := by
  simp only [protocolQueryPrefixCosted, appendProducedCosted_result,
    protocolPrefixCosted_result, protocolQueryPrefix, List.append_assoc]

/-- Public initialization and the copied trace bound the complete query item count. -/
theorem protocolQueryPrefixCosted_length_le {F G : Type*}
    (initial trace : List (TranscriptElt F G)) (index : ℕ) :
    (protocolQueryPrefixCosted initial trace index).1.length ≤ initial.length + trace.length + 1 := by
  have h := protocolPrefixCosted_length_le index trace
  simp only [protocolQueryPrefixCosted, appendProducedCosted_result,
    List.length_append, List.length_cons, List.length_nil]
  omega

/-- Both copied prefixes and the final marker remain in the query-construction cost. -/
theorem protocolQueryPrefixCosted_cost_le {F G : Type*}
    (initial trace : List (TranscriptElt F G)) (index : ℕ) :
    (protocolQueryPrefixCosted initial trace index).2 ≤ 2 * initial.length + 5 * trace.length + 10 := by
  have hc := protocolPrefixCosted_cost_le index trace
  have hl := protocolPrefixCosted_length_le index trace
  simp only [protocolQueryPrefixCosted, appendProducedCosted_cost, appendProducedCosted_result,
    List.length_append]
  omega

/-- Produce every query byte and retain the original fixed personalization. -/
def protocolQueryAddressCosted (read : ℕ) (initial trace : List (TranscriptElt Fp VestaG)) (index : ℕ) :
    TranscriptHashAddress × ℕ :=
  let due := protocolQueryPrefixCosted initial trace index
  let bytes := transcriptBytesCosted read due.1
  ((halo2TranscriptPersonalization, bytes.1), due.2 + bytes.2 + 18)

/-- The counted address is byte-for-byte the original personalized raw-hash address. -/
theorem protocolQueryAddressCosted_result (read : ℕ)
    (initial trace : List (TranscriptElt Fp VestaG)) (index : ℕ) :
    (protocolQueryAddressCosted read initial trace index).1 = protocolQueryAddress initial trace index := by
  simp only [protocolQueryAddressCosted, transcriptBytesCosted_result, protocolQueryPrefixCosted_result,
    protocolQueryAddress, transcriptHashAddress]

/-- The bound includes prefix traversal, every encoded byte, and personalization construction. -/
theorem protocolQueryAddressCosted_cost_le (read : ℕ)
    (initial trace : List (TranscriptElt Fp VestaG)) (index : ℕ) :
    (protocolQueryAddressCosted read initial trace index).2 ≤
      2 * initial.length + 5 * trace.length +
        (initial.length + trace.length + 1) * (64 * (read + 71) + 2154) + 30 := by
  have hp := protocolQueryPrefixCosted_cost_le initial trace index
  have hs := protocolQueryPrefixCosted_length_le initial trace index
  have he := transcriptBytesCosted_cost_le read (protocolQueryPrefixCosted initial trace index).1
  have hb := he.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right (64 * (read + 71) + 2154) hs) 1)
  dsimp only [protocolQueryAddressCosted]
  omega

end Zcash.Snark.ZeroKnowledge
