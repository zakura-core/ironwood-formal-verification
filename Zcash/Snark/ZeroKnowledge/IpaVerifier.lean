import Zcash.Snark.ZeroKnowledge.IpaTranscript
import Zcash.Snark.Soundness.FiatShamir.Assembly

/-!
# Correspondence with the existing IPA verifier

The new honest-prover and simulation model uses recursive coefficient and public-vector
folds. The existing verifier uses `computeS`, `computeB` and a flattened MSM. The established
`foldAll` correspondence lets us prove that the two final equations are identical, rather
than assume that the new transcript satisfies the deployed Lean assembly.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Msm URS)

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The indexed public-generator fold equals the verifier's list fold, connecting the simulator
equation to verification. -/
private theorem publicFold_list (rounds : List F) (g : Fin (2 ^ rounds.length) → G) :
    publicFold rounds.length rounds.get g = foldAll rounds g 0 := by
  induction rounds with
  | nil => rfl
  | cons u rest ih =>
    simp only [List.length_cons]
    rw [publicFold, foldAll, foldGens, inv_inv]
    exact ih _

/-- Reindexing equal-length challenge and generator vectors preserves their public fold, supporting
proof-shape transport. -/
private theorem publicFold_cast {k m : ℕ} (h : m = k)
    (rounds : Fin k → F) (g : Fin (2 ^ k) → G) :
    publicFold m (fun j => rounds (Fin.cast h j))
        (fun j => g (Fin.cast (congrArg (2 ^ ·) h) j)) = publicFold k rounds g := by
  subst h
  rfl

/-- The public fold is the existing verifier's `foldAll`, including the list-length transport. -/
theorem publicFold_eq_foldAll (k : ℕ) (rounds : Fin k → F) (g : Fin (2 ^ k) → G) :
    publicFold k rounds g =
      foldAll (List.ofFn rounds)
        (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) 0 := by
  have hget : (List.ofFn rounds).get = fun j => rounds (Fin.cast List.length_ofFn j) := by
    funext j
    simp only [List.get_ofFn]
  rw [← publicFold_list, hget]
  exact (publicFold_cast List.length_ofFn rounds g).symm

/-- The verifier's `computeS` term uses precisely the generator folded in the simulation. -/
theorem computeS_gterm_publicFold (k : ℕ) (rounds : Fin k → F)
    (g : Fin (2 ^ k) → G) (c : F) :
    (∑ i, (computeS (List.ofFn rounds) (-c)).getD i.val 0 • g i) =
      (-c) • publicFold k rounds g := by
  rw [deployed_gterm_foldAll, publicFold_eq_foldAll]

/-- The verifier's `computeB` is precisely the folded powers vector. -/
theorem publicFold_evalVector (k : ℕ) (rounds : Fin k → F) (q : F) :
    publicFold k rounds (evalVector k q) = computeB q (List.ofFn rounds) := by
  rw [publicFold_eq_foldAll]
  change foldAll (List.ofFn rounds) (evalVector (List.ofFn rounds).length q) 0 = _
  exact foldAll_evalVector q (List.ofFn rounds)

/-- The indexed round sum agrees with the verifier's zipped list sum without truncation. -/
theorem ipaMessageSum_eq_roundSum (k : ℕ) (rounds : Fin k → F)
    (messages : Fin k → G × G) :
    ipaMessageSum rounds messages = roundSum (List.ofFn messages) (List.ofFn rounds) := by
  induction k with
  | zero => simp [ipaMessageSum, roundSum]
  | succ k ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    change ipaMessageSum rounds messages =
      roundSum (((messages 0).1, (messages 0).2) :: List.ofFn (fun j => messages j.succ))
        (rounds 0 :: List.ofFn (fun j => rounds j.succ))
    rw [roundSum_cons, ← ih]
    simp only [ipaMessageSum, Fin.sum_univ_succ]

/-- The singleton correction contributes only the first generator, recovering the verifier's opening
adjustment. -/
private theorem firstGeneratorTerm (k : ℕ) (g : Fin (2 ^ k) → G) (v : F) :
    (∑ i, ([-v].getD i.val 0) • g i) = (-v) • g 0 := by
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    cases h : j.val with
    | zero => exact (hj (Fin.ext h)).elim
    | succ n => simp [List.getD]
  · simp

/-- Public IPA data taken from the existing verifier's incoming MSM and URS. -/
def IpaPublic.ofMsm (urs : URS G) (incoming : Msm urs.k F G) (q v xi z : F)
    (rounds : Fin urs.k → F) : IpaPublic urs.k F G where
  generators := urs.g
  U := urs.u
  W := urs.w
  commitment := incoming.eval urs
  point := q
  value := v
  xi := xi
  z := z
  rounds := rounds

/-- The joint model's final equation is equivalent to zero evaluation of the existing `ipaFold`.

No prover correctness, nonzero challenge or probability hypothesis is used in this
correspondence. The list lengths are fixed by the indexed transcript itself. -/
theorem ipaTranscript_verifier_capstone (urs : URS G) (incoming : Msm urs.k F G)
    (q v xi z : F) (rounds : Fin urs.k → F) (view : IpaTranscript urs.k F G) :
    view.Verifies (IpaPublic.ofMsm urs incoming q v xi z rounds) ↔
      (ipaFold q v view.scalar view.blind xi z (List.ofFn rounds) view.maskCommitment
        (List.ofFn view.messages) incoming).eval urs = 0 := by
  rw [eval_ipaFold, firstGeneratorTerm, computeS_gterm_publicFold,
    ← publicFold_evalVector]
  change view.Verifies (IpaPublic.ofMsm urs incoming q v xi z rounds) ↔
    incoming.eval urs + (-v) • urs.g 0 + xi • view.maskCommitment +
        roundSum (List.ofFn view.messages) (List.ofFn rounds) +
        (-view.scalar * publicFold urs.k rounds (evalVector urs.k q) * z) • urs.u +
        (-view.blind) • urs.w + (-view.scalar) • publicFold urs.k rounds urs.g = 0
  rw [← ipaMessageSum_eq_roundSum]
  unfold IpaTranscript.Verifies IpaPublic.ofMsm ipaPublicResponse
  constructor <;> intro h <;> linear_combination (norm := module) h

/-- Extract exactly the IPA fields from the existing proof-string representation. -/
def IpaTranscript.ofProofString {shape : Shape} (ps : ProofString shape F G) :
    IpaTranscript shape.k F G where
  maskCommitment := ps.ipaS
  messages := ps.ipaRounds
  scalar := ps.ipaC
  blind := ps.ipaF

/-- The same correspondence inside the complete verifier's final MSM assembly.

This result identifies the last equation and its public inputs. It does not prove that the
earlier opening is valid, that its fields have a simulated distribution, or that a rejecting
parser or Fiat–Shamir transcript reaches this assembly. -/
theorem ipaTranscript_assembleFinalMsm {shape : Shape} (g : Fin (2 ^ shape.k) → G)
    (W U : G) (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (grouped : MultiopenGrouped shape.k F G) :
    let opened := assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime
      (List.ofFn ps.multiopenU) grouped (Msm.zero shape.k F G)
    (IpaTranscript.ofProofString ps).Verifies
        (IpaPublic.ofMsm ⟨shape.k, g, W, U⟩ opened.1 ch.x3 opened.2 ch.xi ch.z ch.ipaRound) ↔
      (assembleFinalMsm ps ch grouped).eval ⟨shape.k, g, W, U⟩ = 0 := by
  exact ipaTranscript_verifier_capstone ⟨shape.k, g, W, U⟩ _ _ _ _ _ _ _

end Zcash.Snark.ZeroKnowledge
