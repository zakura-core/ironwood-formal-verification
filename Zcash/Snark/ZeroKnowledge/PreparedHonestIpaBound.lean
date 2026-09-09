import Zcash.Snark.ZeroKnowledge.PreparedHonestIpaCost

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Arithmetic (Fp)
variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Preparation and complete real IPA budget for the original 2048-coefficient opening. -/
def preparedHonestIpaCostBudget (costs : FieldOperationCosts) (groupAdd groupScale equal read
    dataRead access tapeAccess : ℕ) : ℕ :=
  dataRead + densePolynomialCommitmentCostBudget read groupAdd groupScale 2048 2048 access
    (read + 1) (read + 1) access + 5 * access + read + 12 +
    honestIpaTranscriptCostBudget costs groupAdd groupScale equal 11
      (access + 4096 + read + 2 + 2 * tapeAccess + 7)

/-- The bound pays for the commitment producer, stored polynomial reads, and every original IPA coin. -/
theorem preparedHonestIpaCosted_cost_le (costs : FieldOperationCosts) (groupAdd groupScale equal read : ℕ)
    (generators : Fin 2048 → G × ℕ) (W U : G × ℕ) (data : StoredMultiopenData × ℕ)
    (q xi z : Fp × ℕ) (rounds : Fin 11 → Fp × ℕ) (tape : Fin (ipaSampleCount 11) → Fp × ℕ)
    (access tapeAccess : ℕ) (hwidth : data.1.coefficients.length ≤ 2048)
    (hg : ∀ i, (generators i).2 ≤ access) (hr : ∀ i, (rounds i).2 ≤ access)
    (hW : W.2 ≤ access) (hU : U.2 ≤ access) (hq : q.2 ≤ access)
    (hxi : xi.2 ≤ access) (hz : z.2 ≤ access) (ht : ∀ i, (tape i).2 ≤ tapeAccess) :
    (preparedHonestIpaCosted costs groupAdd groupScale equal read generators W U data q xi z rounds tape).2 ≤
      preparedHonestIpaCostBudget costs groupAdd groupScale equal read data.2 access tapeAccess := by
  let commitment := densePolynomialCommitmentCosted read groupAdd groupScale generators W
    (data.1.coefficients, read + 1) (data.1.blind, read + 1)
  let input := prepareIpaPublicCosted generators W U
    ((commitment.1, data.1.value), commitment.2 + read + 1) q xi z rounds
  have hp : input.1.ReadBound (access + 4096 + read + 2) :=
    prepareIpaPublicCosted_readBound _ _ _ _ _ _ _ _ _ (by omega)
      (fun i => (hg i).trans (by omega)) (fun i => (hr i).trans (by omega))
  have hc : ∀ i : Fin 2048,
      (getDListCosted read (0 : Fp) data.1.coefficients i.val).2 ≤ access + 4096 + read + 2 := by
    intro i
    have h := getDListCosted_cost_le read (0 : Fp) data.1.coefficients i.val
    omega
  have hi := honestIpaTranscriptFromTapeCosted_cost_le costs groupAdd groupScale equal input.1
    (fun i => getDListCosted read (0 : Fp) data.1.coefficients i.val) (data.1.blind, read + 1) tape
    (access + 4096 + read + 2) tapeAccess hp hc (by change read + 1 ≤ _; omega) ht
  have hb := densePolynomialCommitmentCosted_cost_le read groupAdd groupScale generators W
    (data.1.coefficients, read + 1) (data.1.blind, read + 1) access hg
  change commitment.2 ≤ densePolynomialCommitmentCostBudget read groupAdd groupScale 2048
    data.1.coefficients.length access (read + 1) (read + 1) W.2 at hb
  have hprepare : input.2 = commitment.2 + read + 1 + W.2 + U.2 + q.2 + xi.2 + z.2 + 10 := rfl
  unfold preparedHonestIpaCosted
  change data.2 + input.2 + (honestIpaTranscriptFromTapeCosted costs groupAdd groupScale equal input.1
    (fun i => getDListCosted read (0 : Fp) data.1.coefficients i.val) (data.1.blind, read + 1) tape).2 + 1 ≤ _
  unfold preparedHonestIpaCostBudget densePolynomialCommitmentCostBudget at *
  omega

end Zcash.Snark.ZeroKnowledge
