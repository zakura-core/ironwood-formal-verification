import Zcash.Snark.Core.Challenges

/-!
# Complete access prices for already prepared verifier challenges

Each scalar retains the cost of its supplied producer or stored-input reader.
The IPA-round family retains the full cost of each indexed access. Constructing
these inputs from a bit tape is a separate preparation stage.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Erase access prices while preserving every original verifier challenge. -/
def Challenges.eraseCosts {k : ℕ} {F : Type*} (ch : Challenges k (F × ℕ)) : Challenges k F where
  theta := ch.theta.1
  beta := ch.beta.1
  gamma := ch.gamma.1
  y := ch.y.1
  x := ch.x.1
  x1 := ch.x1.1
  x2 := ch.x2.1
  x3 := ch.x3.1
  x4 := ch.x4.1
  xi := ch.xi.1
  z := ch.z.1
  ipaRound := fun index => (ch.ipaRound index).1

/-- A common upper bound on every complete challenge access. -/
def Challenges.ReadBound {k : ℕ} {F : Type*} (ch : Challenges k (F × ℕ)) (access : ℕ) : Prop :=
  ch.theta.2 ≤ access ∧ ch.beta.2 ≤ access ∧ ch.gamma.2 ≤ access ∧
    ch.y.2 ≤ access ∧ ch.x.2 ≤ access ∧ ch.x1.2 ≤ access ∧ ch.x2.2 ≤ access ∧
    ch.x3.2 ≤ access ∧ ch.x4.2 ≤ access ∧ ch.xi.2 ≤ access ∧ ch.z.2 ≤ access ∧
    ∀ index, (ch.ipaRound index).2 ≤ access

end Zcash.Snark.ZeroKnowledge
