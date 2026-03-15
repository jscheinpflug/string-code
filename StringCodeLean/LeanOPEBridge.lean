import StringCodeLean.BCGhostTyped

open StringCodeLean.BCGhost

abbrev Coord := Nat

inductive DemoCase where
  | bc
  | cbc
  | bbcc
  deriving DecidableEq, Repr

namespace DemoCase

def parse? : String → Option DemoCase
  | "bc" => some .bc
  | "cbc" => some .cbc
  | "bbcc" => some .bbcc
  | _ => none

end DemoCase

def z : Coord := 0
def z' : Coord := 1
def w : Coord := 2
def w' : Coord := 3

@[simp] def bcAtW : NOProd Coord .holo 0 1 :=
  NOProd.ofRawHolo [RawField.mk .b 0 w, RawField.mk .c 0 w]

@[simp] def bbLeft : NOProd Coord .holo (-2) 5 :=
  NOProd.ofRawHolo [RawField.mk .b 0 z, RawField.mk .b 1 z']

@[simp] def ccRight : NOProd Coord .holo 2 (-2) :=
  NOProd.ofRawHolo [RawField.mk .c 0 w, RawField.mk .c 0 w']

def runCase : DemoCase → List (RawTerm Coord)
  | .bc => (opeField (Field.b 0 z) (NOProd.singleton (Field.c 0 w))).erase
  | .cbc => (opeField (Field.c 0 z) bcAtW).erase
  | .bbcc => (ope bbLeft ccRight).erase

def renderSpecies : Species → String
  | .b => "b"
  | .c => "c"

def renderField (field : RawField Coord) : String :=
  s!"{renderSpecies field.species}:{field.deriv}@{field.coord}"

def renderPole (pole : PoleFactor Coord) : String :=
  s!"({pole.left},{pole.right},{pole.order})"

def renderKernel (kernel : RawKernel Coord) : String :=
  let poles := String.intercalate "," (kernel.poles.map renderPole)
  s!"coeff={kernel.coeff};poles=[{poles}]"

def renderTerm (term : RawTerm Coord) : String :=
  let remainder := String.intercalate "," (term.remainder.map renderField)
  s!"{renderKernel term.kernel};rem=[{remainder}]"

def renderTermsAux : Nat → List (RawTerm Coord) → List String
  | _, [] => []
  | idx, term :: terms => s!"{idx}: {renderTerm term}" :: renderTermsAux (idx + 1) terms

def renderTerms (terms : List (RawTerm Coord)) : String :=
  String.intercalate "\n" (renderTermsAux 0 terms)

@[export lean_ope_case]
def leanOpeCase (caseName : @& String) : String :=
  match DemoCase.parse? caseName with
  | some demoCase => renderTerms (runCase demoCase)
  | none => s!"ERROR: unknown case '{caseName}'. Expected one of: bc, cbc, bbcc."

def mkLeft (n : Nat) :
    NOProd Coord .holo
      (totalGhost (List.range n |>.map fun i => RawField.mk .c 0 i))
      (totalWeight (List.range n |>.map fun i => RawField.mk .c 0 i)) :=
  NOProd.ofRawHolo (List.range n |>.map fun i => RawField.mk .c 0 i)

def mkRight (n : Nat) :
    NOProd Coord .holo
      (totalGhost (List.range n |>.map fun i => RawField.mk .b 0 (n + i)))
      (totalWeight (List.range n |>.map fun i => RawField.mk .b 0 (n + i))) :=
  NOProd.ofRawHolo (List.range n |>.map fun i => RawField.mk .b 0 (n + i))

def benchSummary (n : Nat) : String :=
  let lhs := mkLeft n
  let rhs := mkRight n
  let termCount := (ope lhs rhs).erase.length
  s!"n={n} terms={termCount}"

@[export lean_ope_bench_n]
def leanOpeBenchN (nText : @& String) : String :=
  match String.toNat? nText with
  | some n =>
      if 1 ≤ n ∧ n ≤ 8 then
        benchSummary n
      else
        s!"ERROR: n={n} out of range; expected 1..8."
  | none => s!"ERROR: could not parse n from '{nText}'."
