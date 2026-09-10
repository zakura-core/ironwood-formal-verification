/-!
# Bounded pieces of source-indexed certificates

Each piece records its exact unprocessed source and a checked continuation back
to the original source. Separate declarations can therefore certify a large
program in bounded pieces without weakening its erasure or semantic obligations.
The final composition must provide a certificate for the final remainder.
-/

namespace Zcash.Snark.ZeroKnowledge

universe u v

/-- A source-preserving continuation whose remaining obligation stays explicit. -/
structure SourceCertificatePiece {Entry : Type u} (Certificate : List Entry → Type v)
    (source : List Entry) where
  remaining : List Entry
  finish : Certificate remaining → Certificate source

end Zcash.Snark.ZeroKnowledge
