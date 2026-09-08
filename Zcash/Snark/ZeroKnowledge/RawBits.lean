import Zcash.Snark.ZeroKnowledge.RawFieldTape
import Mathlib.Algebra.BigOperators.Fin

/-!
# Packing a fixed bit tape into raw 512-bit words

An explicit base-two equivalence packs each consecutive 512-bit block in
little-endian order. Uniform bits therefore produce exactly uniform raw words.
The conversion consumes a fixed number of bits and performs no rejection.
-/

namespace Zcash.Snark.ZeroKnowledge

set_option exponentiation.threshold 1024
set_option maxRecDepth 8192

/-- A fixed bit tape, grouped into consecutive little-endian 512-bit words. -/
def rawBitsTapeEquiv (count : ℕ) : (Fin (count * 512) → Bool) ≃ RawFieldTape count :=
  ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin count) (Fin 512) Bool)).trans
      (Equiv.piCongrRight fun _ =>
        (Equiv.arrowCongr (Equiv.refl (Fin 512)) finTwoEquiv.symm).trans finFunctionFinEquiv)

/-- The first bit of each block is its least significant bit. -/
theorem rawBitsTapeEquiv_word {count : ℕ} (bits : Fin (count * 512) → Bool) (word : Fin count) :
    (rawBitsTapeEquiv count bits word).val =
      ∑ bit : Fin 512, (finTwoEquiv.symm (bits (finProdFinEquiv (word, bit)))).val * 2 ^ bit.val :=
  finFunctionFinEquiv_apply _

/-- Independent uniform input bits give exactly the complete uniform raw-word tape. -/
theorem uniformRawBitsTape (count : ℕ) :
    (PMF.uniformOfFintype (Fin (count * 512) → Bool)).map (rawBitsTapeEquiv count) =
      PMF.uniformOfFintype (RawFieldTape count) :=
  Zcash.map_uniformOfFintype_equiv _

/-- Every deterministic raw-tape program has the same law when fed the packed uniform bit tape. -/
theorem rawBitsTape_map {Output : Type*} (count : ℕ) (finish : RawFieldTape count → Output) :
    (PMF.uniformOfFintype (Fin (count * 512) → Bool)).map (finish ∘ rawBitsTapeEquiv count) =
      (PMF.uniformOfFintype (RawFieldTape count)).map finish := by
  have h := congrArg (PMF.map finish) (uniformRawBitsTape count)
  simpa only [PMF.map_comp] using h

end Zcash.Snark.ZeroKnowledge
