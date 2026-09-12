import Zcash.Snark.ZeroKnowledge.PlonkCommitmentCausality
import Zcash.Snark.ZeroKnowledge.IpaCausality

/-!
# IPA causality inside the complete prover

The IPA inputs here are the actual opening, coefficients, and inherited blind
computed from the complete PLONK private material. The private IPA suffix is
the suffix of the same full prover tape. No separate independence assumption
or valid-opening premise is introduced to establish message dependencies.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp URS)
open CompPoly

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The exact IPA computation used by the joint prover, with its private material made explicit. -/
def plonkIpaTranscriptFromMaterial {actions : ℕ} (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly) (material : PlonkPrivateMaterial actions)
    (tape : Fin (ipaSampleCount urs.k) → Fp) : IpaTranscript urs.k Fp G :=
  let data := plonkIpaData urs pub x x1 x2 x4 q xi z rounds pieces material
  ipaTranscriptFromTape data.1 data.2.1 data.2.2 tape

/-- Extracting the actual material and suffix preserves the complete IPA transcript exactly. -/
theorem plonkJointViewFromTape_ipa {actions : ℕ}
    (construct : PrivateColumnId actions → ColumnHistory 2048 → (Fin 2048 → Fp))
    (history : ColumnHistory 2048) (urs : URS G) (pub : PlonkPublicPolynomials actions)
    (x x1 x2 x4 q xi z : Fp) (rounds : Fin urs.k → Fp)
    (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (tape : Fin (plonkJointSampleCount construct urs.k) → Fp) :
    (plonkJointViewFromTape construct history urs pub x x1 x2 x4 q xi z rounds pieces tape).2 =
      plonkIpaTranscriptFromMaterial urs pub x x1 x2 x4 q xi z rounds pieces
        (plonkJointMaterialFromTape construct history tape)
        (splitTapeEquiv (batchedColumnSampleCount (plonkColumnBatches construct) + 12)
          (ipaSampleCount urs.k) Fp tape).2 := rfl

/-- The actual sparse-mask commitment uses the opening point and its own tape, even as private material varies. -/
theorem plonkIpaTranscriptFromMaterial_mask_agrees {actions : ℕ}
    (urs : URS G) (pub : PlonkPublicPolynomials actions) (left right : Challenges urs.k Fp)
    (pieces pieces' : ColumnHistory 2048 → Fin 8 → CPoly)
    (material material' : PlonkPrivateMaterial actions) (tape : Fin (ipaSampleCount urs.k) → Fp)
    (hq : left.x3 = right.x3) :
    (plonkIpaTranscriptFromMaterial urs pub left.x left.x1 left.x2 left.x4 left.x3 left.xi left.z
        left.ipaRound pieces material tape).maskCommitment =
      (plonkIpaTranscriptFromMaterial urs pub right.x right.x1 right.x2 right.x4 right.x3 right.xi right.z
        right.ipaRound pieces' material' tape).maskCommitment := by
  unfold plonkIpaTranscriptFromMaterial
  apply ipaTranscriptFromTape_maskCommitment_agrees
  · simp only [plonkIpaData, computedMultiopenIpaPublic, IpaPublic.ofMsm]
  · simp only [plonkIpaData, computedMultiopenIpaPublic, IpaPublic.ofMsm]
  · simpa only [plonkIpaData, computedMultiopenIpaPublic, IpaPublic.ofMsm] using hq

/-- The computed opening and inherited blind preserve the strict earlier-round dependency. -/
theorem plonkIpaTranscriptFromMaterial_messages_prefix {actions : ℕ}
    (urs : URS G) (pub : PlonkPublicPolynomials actions) (x x1 x2 x4 q xi z : Fp)
    (left right : Fin urs.k → Fp) (pieces : ColumnHistory 2048 → Fin 8 → CPoly)
    (material : PlonkPrivateMaterial actions) (tape : Fin (ipaSampleCount urs.k) → Fp) (j : Fin urs.k)
    (h : ∀ i : Fin urs.k, i.val < j.val → left i = right i) :
    (plonkIpaTranscriptFromMaterial urs pub x x1 x2 x4 q xi z left pieces material tape).messages j =
      (plonkIpaTranscriptFromMaterial urs pub x x1 x2 x4 q xi z right pieces material tape).messages j := by
  let data := plonkIpaData urs pub x x1 x2 x4 q xi z left pieces material
  exact ipaTranscriptFromTape_messages_prefix data.1 right data.2.1 data.2.2 tape j h

/-- The actual proof's S commitment ignores xi, z, and all IPA round challenges. -/
theorem plonkVerifierProofFromTape_mask_causal {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (left right : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness left) urs.k) → Fp)
    (tape' : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness right) urs.k) → Fp)
    (hx3 : left.x3 = right.x3) (htape : TapeAgrees tape tape') :
    (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left
        tape).ipaS =
      (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right
        tape').ipaS := by
  have htail := (plonkJointTape_split_congr _ _ tape tape' htape).2
  change (plonkJointViewFromTape _ [] urs pub left.x left.x1 left.x2 left.x4 left.x3 left.xi left.z
      left.ipaRound (plonkHonestQuotientPieces vk pub left) tape).2.maskCommitment =
    (plonkJointViewFromTape _ [] urs pub right.x right.x1 right.x2 right.x4 right.x3 right.xi right.z
      right.ipaRound (plonkHonestQuotientPieces vk pub right) tape').2.maskCommitment
  rw [plonkJointViewFromTape_ipa, plonkJointViewFromTape_ipa, htail]
  exact plonkIpaTranscriptFromMaterial_mask_agrees _ _ _ _ _ _ _ _ _ hx3

/-- Every actual IPA round pair uses only challenges received before that pair is emitted. -/
theorem plonkVerifierProofFromTape_round_causal {actions : ℕ}
    (urs : URS G) (vk : VerifyingKey (plonkProofShape actions urs.k) Fp G)
    (pub : PlonkPublicPolynomials actions) (witness : Fin actions → Fin 10 → Fin 2048 → Fp)
    (left right : Challenges urs.k Fp)
    (tape : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness left) urs.k) → Fp)
    (tape' : Fin (plonkJointSampleCount (plonkTotalColumnConstructor vk pub witness right) urs.k) → Fp)
    (htheta : left.theta = right.theta) (hbeta : left.beta = right.beta) (hgamma : left.gamma = right.gamma)
    (hy : left.y = right.y) (hx : left.x = right.x) (hx1 : left.x1 = right.x1) (hx2 : left.x2 = right.x2)
    (hx3 : left.x3 = right.x3) (hx4 : left.x4 = right.x4) (hxi : left.xi = right.xi) (hz : left.z = right.z)
    (j : Fin urs.k) (hrounds : ∀ i : Fin urs.k, i.val < j.val → left.ipaRound i = right.ipaRound i)
    (htape : TapeAgrees tape tape') :
    (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness left) [] urs vk pub left tape).ipaRounds j =
      (plonkVerifierProofFromTape (plonkTotalColumnConstructor vk pub witness right) [] urs vk pub right tape').ipaRounds j := by
  have hmaterial := plonkJointMaterialFromTape_congr _ _ [] tape tape'
    (plonkTotalColumnConstructor_challenges vk pub witness left right htheta hbeta hgamma) htape
  have hpieces : plonkHonestQuotientPieces vk pub left = plonkHonestQuotientPieces vk pub right :=
    funext fun rows => plonkHonestQuotientPieces_challenges vk pub left right rows htheta hbeta hgamma hy
  have htail := (plonkJointTape_split_congr _ _ tape tape' htape).2
  change (plonkJointViewFromTape _ [] urs pub left.x left.x1 left.x2 left.x4 left.x3 left.xi left.z
      left.ipaRound (plonkHonestQuotientPieces vk pub left) tape).2.messages j =
    (plonkJointViewFromTape _ [] urs pub right.x right.x1 right.x2 right.x4 right.x3 right.xi right.z
      right.ipaRound (plonkHonestQuotientPieces vk pub right) tape').2.messages j
  rw [plonkJointViewFromTape_ipa, plonkJointViewFromTape_ipa]
  simp only [hmaterial, hpieces, htail, hx, hx1, hx2, hx3, hx4, hxi, hz]
  exact plonkIpaTranscriptFromMaterial_messages_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hrounds

end Zcash.Snark.ZeroKnowledge
