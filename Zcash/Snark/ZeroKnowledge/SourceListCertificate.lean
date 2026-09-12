import Mathlib.Data.List.Basic

/-!
# Exact finite metadata from an original source list

The certificate retains directly evaluable entries and their equality to the
original source projection. Changing source syntax changes only the equality
proof. This interface supports gate and lookup routing metadata without equating
names or indices to semantic constraints without a separate proof.
-/

namespace Zcash.Snark.ZeroKnowledge

/-- A finite list and its exact equality to the original source projection. -/
structure SourceListCertificate {α : Type} (source : List α) where
  entries : List α
  source_eq : entries = source

/-- The exact certificate for an empty source projection. -/
def SourceListCertificate.nil {α : Type} : SourceListCertificate ([] : List α) :=
  ⟨[], rfl⟩

/-- Normalize one metadata entry only with a proof that its value is unchanged. -/
def SourceListCertificate.cons {α : Type} (original value : α)
    (equal : value = original) {rest : List α} (tail : SourceListCertificate rest) :
    SourceListCertificate (original :: rest) :=
  ⟨value :: tail.entries, congrArg₂ List.cons equal tail.source_eq⟩

/-- Transport the source expression while retaining directly evaluable entries. -/
def SourceListCertificate.transport {α : Type} {left right : List α}
    (equal : left = right) (certificate : SourceListCertificate left) :
    SourceListCertificate right :=
  ⟨certificate.entries, certificate.source_eq.trans equal⟩

end Zcash.Snark.ZeroKnowledge
