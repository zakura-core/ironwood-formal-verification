import Zcash.Snark.ZeroKnowledge.IpaTapeCost

namespace Zcash.Snark.ZeroKnowledge

/-- A larger explicit bound still covers every original public-input reader. -/
theorem IpaPublicCosted.readBound_mono {F G : Type*} {k small large : ℕ}
    {pub : IpaPublicCosted k F G} (h : pub.ReadBound small) (hle : small ≤ large) : pub.ReadBound large := by
  rcases h with ⟨hg, hr, hU, hW, hc, hp, hv, hx, hz⟩
  exact ⟨fun i => (hg i).trans hle, fun i => (hr i).trans hle,
    hU.trans hle, hW.trans hle, hc.trans hle, hp.trans hle, hv.trans hle, hx.trans hle, hz.trans hle⟩

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Decode the original IPA suffix and materialize the complete real transcript. -/
@[irreducible] def honestIpaTranscriptFromTapeCosted
    (costs : FieldOperationCosts) (groupAdd groupScale equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (rho : F × ℕ) (tape : Fin (ipaSampleCount k) → F × ℕ) : MaterializedIpaTranscript F G × ℕ :=
  materializeIpaCosted (honestIpaTranscriptCosted costs groupAdd groupScale equal pub coefficients rho
    (ipaAlphaTapeCosted tape) (ipaMaskTapeCosted tape) (ipaRoundTapeCosted tape))

/-- The full counted execution has exactly the original tape-driven IPA observation. -/
theorem honestIpaTranscriptFromTapeCosted_result
    (costs : FieldOperationCosts) (groupAdd groupScale equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (rho : F × ℕ) (tape : Fin (ipaSampleCount k) → F × ℕ) :
    (honestIpaTranscriptFromTapeCosted costs groupAdd groupScale equal pub coefficients rho tape).1 =
      materializedIpaTranscript (ipaTranscriptFromTape pub.erase (fun i => (coefficients i).1) rho.1
        (fun i => (tape i).1)) := by
  unfold honestIpaTranscriptFromTapeCosted
  rewrite [materializedHonestIpaCosted_result]
  simp only [ipaAlphaTapeCosted_result, ipaMaskTapeCosted_result, ipaRoundTapeCosted_result, ipaTranscriptFromTape]

/-- Full real IPA bound includes the original tape layout and every output, with no validity premise. -/
theorem honestIpaTranscriptFromTapeCosted_cost_le
    (costs : FieldOperationCosts) (groupAdd groupScale equal : ℕ) {k : ℕ}
    (pub : IpaPublicCosted k F G) (coefficients : Fin (2 ^ k) → F × ℕ)
    (rho : F × ℕ) (tape : Fin (ipaSampleCount k) → F × ℕ) (access tapeAccess : ℕ)
    (hpub : pub.ReadBound access) (hc : ∀ i, (coefficients i).2 ≤ access)
    (hrho : rho.2 ≤ access) (ht : ∀ i, (tape i).2 ≤ tapeAccess) :
    (honestIpaTranscriptFromTapeCosted costs groupAdd groupScale equal pub coefficients rho tape).2 ≤
      honestIpaTranscriptCostBudget costs groupAdd groupScale equal k (access + 2 * tapeAccess + 7) := by
  unfold honestIpaTranscriptFromTapeCosted
  apply materializedHonestIpaCosted_cost_le
  · exact IpaPublicCosted.readBound_mono hpub (by omega)
  · intro i; have h := hc i; omega
  · omega
  · intro i; have h := ipaAlphaTapeCosted_cost_le tape tapeAccess ht i; omega
  · have h := ipaMaskTapeCosted_cost_le tape tapeAccess ht; omega
  · intro i; have h := ipaRoundTapeCosted_cost_le tape tapeAccess ht i; omega

end Zcash.Snark.ZeroKnowledge
