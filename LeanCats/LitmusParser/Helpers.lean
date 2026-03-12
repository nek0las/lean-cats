/-
  LitmusParser/Helpers.lean — String-level parser helpers and generic (architecture-independent)
  parsers for litmus test formats.
-/
import LeanCats.LitmusParser.Types

namespace LitmusParser

-- ════════════════════════════════════════════════════════════════
-- String Utilities
-- ════════════════════════════════════════════════════════════════

/-- Helper: trim whitespace, returning String (not Slice). -/
def strim (s : String) : String := s.trimAscii.toString

/-- Helper: drop prefix, returning String. -/
def sdropPrefix (s : String) (pfx : String) : String :=
  if s.startsWith pfx then (s.drop pfx.length).toString else s

/-- Helper: drop suffix, returning String. -/
def sdropSuffix (s : String) (sfx : String) : String :=
  if s.endsWith sfx then (s.take (s.length - sfx.length)).toString else s

/-- Extract text between the first occurrence of `open_` and the matching `close_`. -/
def extractBetween (s : String) (open_ close_ : Char) : Option String := Id.run do
  let mut inside := false
  let mut acc : String := ""
  for c in s.toList do
    if !inside then
      if c == open_ then inside := true
    else
      if c == close_ then return some acc
      acc := acc.push c
  return none

/-- Check if a string contains a given substring. -/
def scontains (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Parse a natural number from a string (only digits). -/
def parseNat (s : String) : Option Nat :=
  let digits := s.toList.filter Char.isDigit
  if digits.isEmpty then none
  else some (digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0)

/-- Look up the index of a location name in a location array. -/
def locIndex (locs : Array String) (name : String) : Nat :=
  match locs.findIdx? (· == name) with
  | some i => i
  | none   => locs.size

-- ════════════════════════════════════════════════════════════════
-- Generic Parsers (shared across architectures)
-- ════════════════════════════════════════════════════════════════

/-- Parse initial state: `{ x=0; y=0; }` → `[("x", 0), ("y", 0)]` -/
def parseInitState (line : String) : Array (String × Nat) := Id.run do
  let some inner := extractBetween line '{' '}'
    | return #[]
  let parts := inner.splitOn ";"
  let mut result : Array (String × Nat) := #[]
  for part in parts do
    let trimmed := strim part
    if trimmed.isEmpty then continue
    let eqParts := trimmed.splitOn "="
    if eqParts.length ≥ 2 then
      let locName := strim eqParts[0]!
      let valStr  := strim eqParts[1]!
      if let some val := parseNat valStr then
        result := result.push (locName, val)
  return result

/-- Parse the exists clause: `exists (0:EAX=0 /\ 1:EAX=0)` -/
def parseExists (line : String) : ExistsConstraint := Id.run do
  let some inner := extractBetween line '(' ')'
    | return { conjuncts := #[] }
  -- Split on "/\"
  let parts := inner.splitOn "/\\"
  let mut conjuncts : Array ExistsConjunct := #[]
  for part in parts do
    let p := strim part
    let colonParts := p.splitOn ":"
    if colonParts.length < 2 then continue
    let tidStr := strim colonParts[0]!
    let rest := strim colonParts[1]!
    let eqParts := rest.splitOn "="
    if eqParts.length < 2 then continue
    let reg := strim eqParts[0]!
    let valStr := strim eqParts[1]!
    if let some tid := parseNat tidStr then
      if let some val := parseNat valStr then
        conjuncts := conjuncts.push { tid, reg, val }
  return { conjuncts }

end LitmusParser
