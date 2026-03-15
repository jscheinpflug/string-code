import StringCodeLean.BCGhostTyped
import Std

open StringCodeLean.BCGhost

abbrev Coord := Nat

def mkLeft (n : Nat) : NOProd Coord .holo (totalGhost (List.range n |>.map fun i => RawField.mk .c 0 i)) (totalWeight (List.range n |>.map fun i => RawField.mk .c 0 i)) :=
  NOProd.ofRawHolo (List.range n |>.map fun i => RawField.mk .c 0 i)

def mkRight (n : Nat) : NOProd Coord .holo (totalGhost (List.range n |>.map fun i => RawField.mk .b 0 (n + i))) (totalWeight (List.range n |>.map fun i => RawField.mk .b 0 (n + i))) :=
  NOProd.ofRawHolo (List.range n |>.map fun i => RawField.mk .b 0 (n + i))

def defaultRepeats (n : Nat) : Nat :=
  if n ≤ 3 then
    1000
  else if n ≤ 5 then
    100
  else if n ≤ 7 then
    10
  else
    1

def formatMs (ns : Nat) : String :=
  let ms := ns / 1000000
  let frac := (ns / 1000) % 1000
  let fracStr := toString frac
  let fracStr :=
    if frac < 10 then
      "00" ++ fracStr
    else if frac < 100 then
      "0" ++ fracStr
    else
      fracStr
  s!"{ms}.{fracStr}"

def benchmarkOnce (n : Nat) (repeats : Nat := defaultRepeats n) : IO Unit := do
  let lhs := mkLeft n
  let rhs := mkRight n
  let termCount := (ope lhs rhs).erase.length
  let start <- IO.monoNanosNow
  let mut checksum := 0
  for _ in List.range repeats do
    checksum := checksum + (ope lhs rhs).erase.length
  let stop <- IO.monoNanosNow
  let totalNs := stop - start
  let avgNs := totalNs / repeats
  if checksum != repeats * termCount then
    throw <| IO.userError s!"unexpected checksum mismatch for n={n}"
  IO.println s!"n={n} terms={termCount} repeats={repeats} total_ms={formatMs totalNs} avg_ms={formatMs avgNs}"

def parseNatList (args : List String) : List Nat :=
  args.filterMap String.toNat?

def parseRepeats? : List String → Option Nat
  | [] => none
  | "--repeats" :: n :: _ => String.toNat? n
  | "-r" :: n :: _ => String.toNat? n
  | _ :: rest => parseRepeats? rest

def stripRepeatArgs : List String → List String
  | [] => []
  | "--repeats" :: _ :: rest => stripRepeatArgs rest
  | "-r" :: _ :: rest => stripRepeatArgs rest
  | arg :: rest => arg :: stripRepeatArgs rest

def main (args : List String) : IO Unit := do
  let repeats? := parseRepeats? args
  let args := stripRepeatArgs args
  let ns :=
    match parseNatList args with
    | [] => [1, 2, 3, 4, 5, 6, 7]
    | xs => xs
  for n in ns do
    benchmarkOnce n (repeats?.getD (defaultRepeats n))
