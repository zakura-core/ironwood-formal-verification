import Zcash.Snark.ZeroKnowledge.ProofFieldReadCost

/-!
# Retaining record preparation in complete proof-field readers

Each accessed field pays for the complete original record producer. Charging that
producer again at another field is conservative and avoids hiding preparation
inside a function-valued proof record.
-/

namespace Zcash.Snark.ZeroKnowledge
open Zcash.Snark

/-- Attach the complete permutation-record preparation to every present scalar reader. -/
def payPermSetProducer {F : Type*} (producer : PermSetEval (F × ℕ) × ℕ) : PermSetEval (F × ℕ) :=
  producer.1.map (fun value => (value.1, producer.2 + value.2 + 1))

/-- Charging preparation preserves every value and the exact optional-field branch. -/
theorem payPermSetProducer_result {F : Type*} (producer : PermSetEval (F × ℕ) × ℕ) :
    (payPermSetProducer producer).map Prod.fst = producer.1.map Prod.fst := by
  simp only [payPermSetProducer, PermSetEval.map, Option.map_map, Function.comp_def]

/-- Complete permutation-field prices include both preparation and the stored read. -/
theorem payPermSetProducer_readBound {F : Type*} (producer : PermSetEval (F × ℕ) × ℕ)
    (preparation access : ℕ) (hcost : producer.2 ≤ preparation)
    (hread : permSetReadBound producer.1 access) :
    permSetReadBound (payPermSetProducer producer) (preparation + access + 1) := by
  rcases hread with ⟨heval, hnext, hlast⟩
  simp only [payPermSetProducer, permSetReadBound, PermSetEval.map]
  refine ⟨by omega, by omega, ?_⟩
  intro value hvalue
  rcases Option.mem_map.mp hvalue with ⟨original, horiginal, rfl⟩
  have h := hlast original horiginal
  omega

/-- Attach the complete lookup-record preparation to all five scalar readers. -/
def payLookupProducer {F : Type*} (producer : LookupEval (F × ℕ) × ℕ) : LookupEval (F × ℕ) :=
  producer.1.map (fun value => (value.1, producer.2 + value.2 + 1))

/-- All five lookup values remain unchanged after charging their producer. -/
theorem payLookupProducer_result {F : Type*} (producer : LookupEval (F × ℕ) × ℕ) :
    (payLookupProducer producer).map Prod.fst = producer.1.map Prod.fst := rfl

/-- Every lookup-field price retains complete preparation and its actual stored read. -/
theorem payLookupProducer_readBound {F : Type*} (producer : LookupEval (F × ℕ) × ℕ)
    (preparation access : ℕ) (hcost : producer.2 ≤ preparation)
    (hread : lookupEvalReadBound producer.1 access) :
    lookupEvalReadBound (payLookupProducer producer) (preparation + access + 1) := by
  rcases hread with ⟨h0, h1, h2, h3, h4⟩
  simp only [payLookupProducer, lookupEvalReadBound, LookupEval.map]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

end Zcash.Snark.ZeroKnowledge
