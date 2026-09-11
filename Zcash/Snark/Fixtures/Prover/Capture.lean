import Zcash.Snark.Core.Vesta
import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.ZeroKnowledge.RawFieldTape

/-!
# Decoding the Rust prover's observational capture

This decoder accepts the two successful PostNu6_3 fixture profiles. It checks
canonical field encodings, curve membership, dimensions, operation tags, draw
counts at challenge boundaries, and a final success record. The raw RNG words
are packed little-endian and reduced by the model's existing raw-tape boundary.
Expected transcript messages remain separate from the replay's inputs.
-/

namespace Zcash.Snark.Fixtures.Prover

open Zcash.Arithmetic (Fp scalarFieldOrder)
open Zcash.Snark.ZeroKnowledge
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass

/-- Private inputs and public setup captured before the prover randomizes witness tails. -/
structure CaptureInputs where
  actions : ℕ
  generators : Array VestaG
  w : VestaG
  u : VestaG
  fixed : Array (Array Fp)
  sigma : Array (Array Fp)
  instances : Array (Array Fp)
  witness : Array (Array (Array Fp))
  rawTape : List (Fin challengeDigestCard)
  challenges : Array Fp

/-- Outputs are stored separately so replay cannot use the messages it must reproduce. -/
structure Capture where
  inputs : CaptureInputs
  initialization : List (TranscriptElt Fp VestaG)
  messages : List (TranscriptElt Fp VestaG)

private structure Cursor where
  bytes : ByteArray
  offset : ℕ

private abbrev DecodeM := StateT Cursor (Except String)

/-- A checked slice never substitutes zeros for truncated input. -/
private def takeBytes (size : ℕ) : DecodeM ByteArray := do
  let cursor ← get
  if cursor.offset + size > cursor.bytes.size then throw "truncated capture"
  set { cursor with offset := cursor.offset + size }
  return cursor.bytes.extract cursor.offset (cursor.offset + size)

/-- Wire integers use the same little-endian convention as the Rust exporter. -/
private def littleEndian (bytes : ByteArray) : ℕ :=
  bytes.data.foldr (fun byte rest => byte.toNat + 256 * rest) 0

/-- Decode a fixed-width integer after checking that every byte is present. -/
private def readNat (bytes : ℕ) : DecodeM ℕ :=
  return littleEndian (← takeBytes bytes)

/-- Dimensions must match the supported profile before any array is allocated. -/
private def dimension (expected : ℕ) : DecodeM Unit := do
  unless (← readNat 4) == expected do throw "unsupported capture dimension"

/-- Scalar encodings are canonical, so malformed integers cannot silently reduce modulo p. -/
private def readFp : DecodeM Fp := do
  let value ← readNat 32
  if value < scalarFieldOrder then return (value : Fp)
  else throw "noncanonical scalar encoding"

/-- Coordinates are canonical elements of Vesta's base field. -/
private def readFq : DecodeM VestaBaseField := do
  let value ← readNat 32
  if value < PALLAS_SCALAR_CARD then return (value : VestaBaseField)
  else throw "noncanonical coordinate encoding"

/-- A point is accepted only with an explicit identity tag or a checked curve equation. -/
private def readPoint : DecodeM VestaG := do
  match ← readNat 1 with
  | 0 => return 0
  | 1 =>
    let x ← readFq
    let y ← readFq
    if h : OnCurve Vesta.a Vesta.b (x, y) then return ⟨x, y, Or.inl h⟩
    else throw "point is not on Vesta"
  | _ => throw "invalid point tag"

/-- A bounded array of scalar rows, including its encoded length. -/
private def readFields (size : ℕ) : DecodeM (Array Fp) := do
  dimension size
  let mut values := #[]
  for _ in [:size] do values := values.push (← readFp)
  return values

/-- A bounded matrix retains the Rust column-major order. -/
private def readMatrix (columns : ℕ) : DecodeM (Array (Array Fp)) := do
  dimension columns
  let mut values := #[]
  for _ in [:columns] do values := values.push (← readFields 2048)
  return values

/-- Run a payload parser and reject bytes left outside the expected encoding. -/
private def payload {α : Type} (parser : DecodeM α) (bytes : ByteArray) : Except String α := do
  let (value, cursor) ← parser.run ⟨bytes, 0⟩
  unless cursor.offset == bytes.size do throw "trailing record payload"
  return value

private structure Record where
  tag : ℕ
  bytes : ByteArray

/-- The bounded record reader rejects unknown versions, truncated frames, and excessive streams. -/
private def readRecords : DecodeM (Array Record) := do
  unless (← takeBytes 8) == "IZKCAP01".toUTF8 do throw "unsupported capture version"
  let mut records := #[]
  -- The two-Action profile has fewer than 4096 records, including every u64 draw.
  for _ in [:4096] do
    let cursor ← get
    if cursor.offset == cursor.bytes.size then return records
    let tag ← readNat 1
    let size ← readNat 4
    records := records.push ⟨tag, ← takeBytes size⟩
  throw "too many capture records"

/-- Read one required operation without allowing missing records or a different tag. -/
private def required (records : Array Record) (index tag : ℕ) : Except String ByteArray := do
  let some record := records[index]? | throw "missing capture record"
  unless record.tag == tag do throw s!"unexpected operation at record {index}"
  return record.bytes

private structure Setup where
  generators : Array VestaG
  w : VestaG
  u : VestaG
  fixed : Array (Array Fp)
  instances : Array (Array Fp)

/-- Decode only the released circuit dimensions and its actual commitment bases. -/
private def readSetup (actions : ℕ) : DecodeM Setup := do
  dimension 11
  dimension 2048
  dimension 5
  dimension 9
  dimension 2048
  let mut generators := #[]
  for _ in [:2048] do generators := generators.push (← readPoint)
  let w ← readPoint
  let u ← readPoint
  let fixed ← readMatrix 29
  dimension actions
  let mut instances := #[]
  for _ in [:actions] do
    dimension 1
    instances := instances.push (← readFields 10)
  return ⟨generators, w, u, fixed, instances⟩

/-- Witness rows are inputs from Rust synthesis; the replay computes every private mask itself. -/
private def readWitness (actions : ℕ) : DecodeM (Array (Array (Array Fp))) := do
  dimension actions
  let mut witness := #[]
  for _ in [:actions] do witness := witness.push (← readMatrix 10)
  return witness

/-- Successful captures cannot contain rejected transcript operations. -/
private def requireSuccess : DecodeM Unit := do
  unless (← readNat 1) == 1 do throw "rejected transcript operation in successful capture"

/-- The successful profile requires every absorbed or written point to be encodable. -/
private def successfulPoint : DecodeM VestaG := do
  requireSuccess
  let point ← readPoint
  if point = 0 then throw "identity point in successful capture"
  return point

/-- Decode the value actually passed to a successful scalar operation. -/
private def successfulScalar : DecodeM Fp := do
  requireSuccess
  readFp

/-- Pack exactly eight consecutive original u64 results into each bounded 512-bit raw word. -/
private def packWords (words : Array ℕ) : Except String (List (Fin challengeDigestCard)) := do
  unless words.size % 8 == 0 do throw "incomplete wide RNG draw"
  let mut result := #[]
  for index in [:words.size / 8] do
    let value := (words.extract (8 * index) (8 * (index + 1))).foldr
      (fun word rest => word + 2 ^ 64 * rest) 0
    if h : value < challengeDigestCard then result := result.push ⟨value, h⟩
    else throw "wide RNG word exceeds 512 bits"
  return result.toList

/-- The fixed stage boundaries count raw u64 calls, including all discarded and final-mask draws. -/
def challengeDrawCounts (actions : ℕ) : List ℕ :=
  ([70 * actions, 112 * actions, 112 * actions,
    148 * actions + 3, 148 * actions + 11, 148 * actions + 11, 148 * actions + 11,
    148 * actions + 12, 148 * actions + 12, 148 * actions + 24, 148 * actions + 24] ++
    (List.range 11).map (fun round => 148 * actions + 26 + 2 * round)).map (8 * ·)

/-- Decode one complete successful call, preserving separate input and output records. -/
def decodeCapture (actions : ℕ) (bytes : ByteArray) : Except String Capture := do
  unless actions == 1 || actions == 2 do throw "unsupported Action count"
  if bytes.size > 8000000 then throw "capture exceeds supported size"
  let records ← payload readRecords bytes
  let initialScalar ← payload successfulScalar (← required records 0 21)
  let setup ← payload (readSetup actions) (← required records 1 1)
  let sigma ← payload (readMatrix 15) (← required records 2 2)
  let mut initialization := [TranscriptElt.scalar initialScalar]
  for index in [:actions] do
    let point ← payload successfulPoint (← required records (3 + index) 20)
    initialization := initialization ++ [.point point]
  let witness ← payload (readWitness actions) (← required records (3 + actions) 3)
  let terminal ← required records (records.size - 1) 30
  unless terminal.isEmpty do throw "unexpected terminal payload"
  let mut words := #[]
  let mut challenges := #[]
  let mut boundaries := #[]
  let mut messages := #[]
  let mut points := 0
  let mut scalars := 0
  for record in records.extract (4 + actions) (records.size - 1) do
    match record.tag with
    | 11 => words := words.push (← payload (readNat 8) record.bytes)
    | 22 =>
      messages := messages.push (.point (← payload successfulPoint record.bytes))
      points := points + 1
    | 23 =>
      messages := messages.push (.scalar (← payload successfulScalar record.bytes))
      scalars := scalars + 1
    | 24 =>
      challenges := challenges.push (← payload readFp record.bytes)
      boundaries := boundaries.push words.size
      messages := messages.push .challenge
    | _ => throw "unsupported operation in successful prover call"
  unless words.size == 8 * (148 * actions + 46) do throw "wrong RNG draw count"
  unless challenges.size == 22 do throw "wrong challenge count"
  unless boundaries.toList == challengeDrawCounts actions do throw "RNG stage boundary mismatch"
  unless points == 22 * actions + 33 && scalars == 49 * actions + 52 do
    throw "incomplete prover message inventory"
  let rawTape ← packWords words
  return {
    inputs := ⟨actions, setup.generators, setup.w, setup.u, setup.fixed, sigma,
      setup.instances, witness, rawTape, challenges⟩
    initialization := initialization
    messages := messages.toList }

end Zcash.Snark.Fixtures.Prover
