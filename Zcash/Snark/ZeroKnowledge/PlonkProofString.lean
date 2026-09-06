import Zcash.Snark.ZeroKnowledge.PlonkCommitments
import Zcash.Snark.ZeroKnowledge.IpaTranscript
import Zcash.Snark.Verifier.OrchardShape

/-!
# The simulated view in the verifier's proof type

The common constructor below puts the column claims, commitment slots, multi-opening
values, and IPA tail into the existing `ProofString`. Its scalar arguments are generic
so that the same query layout can also hold rotated coefficient polynomials.

`plonkVerifierHx` uses the verifier's actual constraint evaluator. It reads only the
public statement, key, challenges, and the first four column observations. Group points,
the linear mask, the later multi-opening values, and the IPA tail do not enter this
calculation. This fact follows from the existing evaluator's definitions.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)

/-- The captured circuit dimensions, allowing the IPA round count to follow its typed input. -/
def plonkProofShape (actions k : ℕ) : Shape :=
  { FixtureMax.shape actions with k := k }

/-- At eleven rounds this is exactly the existing captured Orchard shape. -/
theorem plonkProofShape_eleven (actions : ℕ) :
    plonkProofShape actions 11 = FixtureMax.shape actions := rfl

/-- Package the pinned query and commitment order into the existing verifier proof type. -/
def plonkProofString {actions k : ℕ} {F G : Type*}
    (instances : Fin actions → F) (fixed : Fin 29 → F) (sigma : Fin 15 → F)
    (column : PrivateColumnId actions → Fin 4 → F)
    (points : Fin (22 * actions + 10) → G) (rEval : F) (groupValues : Fin 5 → F)
    (tail : IpaTranscript k F G) : ProofString (plonkProofShape actions k) F G where
  adviceCommitments := fun a c => plonkColumnEntry points (.advice a c)
  lookupPermutedInput := fun a l => plonkColumnEntry points (.lookupInput a l)
  lookupPermutedTable := fun a l => plonkColumnEntry points (.lookupTable a l)
  permutationProduct := fun a s => plonkColumnEntry points (.permutationProduct a s)
  lookupProduct := fun a l => plonkColumnEntry points (.lookupProduct a l)
  vanishingRandom := plonkLinearEntry points
  hPieces := plonkPieceEntry points
  instanceEvals := fun a _ => instances a
  adviceEvals := fun a j =>
    let query := plonkAdviceQueryOrder j
    column (.advice a query.1) (query.2.castLE (by decide))
  fixedEvals := fun j => fixed (plonkFixedQueryOrder j)
  vanishingRandomEval := rEval
  permutationCommonEvals := sigma
  permutationSetEvals := fun a s =>
    { eval := column (.permutationProduct a s) 0
      nextEval := column (.permutationProduct a s) 1
      lastEval := if s.val < 2 then some (column (.permutationProduct a s) 3) else none }
  lookupEvals := fun a l =>
    { productEval := column (.lookupProduct a l) 0
      productNextEval := column (.lookupProduct a l) 1
      permutedInputEval := column (.lookupInput a l) 0
      permutedInputInvEval := column (.lookupInput a l) 2
      permutedTableEval := column (.lookupTable a l) 0 }
  multiopenQPrime := plonkQuotientPrimeEntry points
  multiopenU := groupValues
  ipaS := tail.maskCommitment
  ipaRounds := tail.messages
  ipaC := tail.scalar
  ipaF := tail.blind

/-- A proof carrying just the claims the constraint evaluator reads; every unused slot is zero. -/
def plonkClaimProof {actions k : ℕ} {F G : Type*} [Zero F] [Zero G]
    (instances : Fin actions → F) (fixed : Fin 29 → F) (sigma : Fin 15 → F)
    (column : PrivateColumnId actions → Fin 4 → F) :
    ProofString (plonkProofShape actions k) F G :=
  plonkProofString instances fixed sigma column (fun _ => 0) 0 (fun _ => 0)
    { maskCommitment := 0, messages := fun _ => (0, 0), scalar := 0, blind := 0 }

/-- The actual constraint list is independent of every omitted group and scalar slot. -/
theorem plonkProofString_allExpressions {actions k : ℕ} {F G : Type*} [Field F] [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) F G) (ch : Challenges k F)
    (instances : Fin actions → F) (fixed : Fin 29 → F) (sigma : Fin 15 → F)
    (column : PrivateColumnId actions → Fin 4 → F)
    (points : Fin (22 * actions + 10) → G) (rEval : F) (groupValues : Fin 5 → F)
    (tail : IpaTranscript k F G) (l0 lLast lBlind : F) :
    allExpressions vk (plonkProofString instances fixed sigma column points rEval groupValues tail)
        ch l0 lLast lBlind =
      allExpressions vk (plonkClaimProof instances fixed sigma column) ch l0 lLast lBlind := rfl

/-- Project the enriched joint view to the exact algebraic fields consumed by the verifier. -/
def plonkProofFromJointView {actions k : ℕ} {G : Type*}
    (pub : PlonkPublicPolynomials actions) (x x1 : Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G) :
    ProofString (plonkProofShape actions k) Fp G :=
  plonkProofString (fun a => (pub.instances a).eval x) (fun c => (pub.fixed c).eval x)
    (fun c => (pub.sigma c).eval x)
    (fun id i => privateColumnView view.1.2.1 id i.castSucc)
    view.1.1 view.1.2.2.1 (plonkPreIpaProjection pub x x1 view.1).groupValues view.2

/-- The verifier's inferred quotient value, computed solely from public column claims. -/
def plonkVerifierHx {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp) (column : PrivateColumnId actions → Fin 5 → Fp) : Fp :=
  let ps : ProofString (plonkProofShape actions k) Fp G :=
    plonkClaimProof (fun a => (pub.instances a).eval ch.x) (fun c => (pub.fixed c).eval ch.x)
      (fun c => (pub.sigma c).eval ch.x) (fun id i => column id i.castSucc)
  let lb := lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x
  expectedHEval (allExpressions vk ps ch lb.1 lb.2.1 lb.2.2) ch.y (ch.x ^ vk.n)

/-- Reconstructing the typed proof preserves exactly the verifier's quotient calculation. -/
theorem plonkVerifierHx_proof {actions k : ℕ} {G : Type*} [Zero G]
    (vk : VerifyingKey (plonkProofShape actions k) Fp G) (pub : PlonkPublicPolynomials actions)
    (ch : Challenges k Fp)
    (view : PreIpaMaskView 5 (22 * actions + 10) G × IpaTranscript k Fp G) :
    let lb := lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x
    expectedHEval (allExpressions vk (plonkProofFromJointView pub ch.x ch.x1 view)
        ch lb.1 lb.2.1 lb.2.2) ch.y (ch.x ^ vk.n) =
      plonkVerifierHx vk pub ch (privateColumnView view.1.2.1) := rfl

end Zcash.Snark.ZeroKnowledge
