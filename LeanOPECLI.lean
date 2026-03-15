import StringCodeLean.BCGhostTyped
import Std

open StringCodeLean.BCGhost

abbrev Coord := Nat

inductive DemoCase where
  | bc
  | cbc
  | bbcc
  deriving DecidableEq, Repr

namespace DemoCase

def all : List DemoCase := [.bc, .cbc, .bbcc]

def name : DemoCase → String
  | .bc => "bc"
  | .cbc => "cbc"
  | .bbcc => "bbcc"

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

def printCase (demoCase : DemoCase) : IO Unit := do
  IO.println s!"case={demoCase.name}"
  IO.println (renderTerms (runCase demoCase))

def usage : String :=
  "usage: lean-ope-cli <bc|cbc|bbcc|all>"

def main (args : List String) : IO Unit := do
  match args with
  | [arg] =>
      if arg = "all" then
        for demoCase in DemoCase.all do
          printCase demoCase
          IO.println ""
      else
        match DemoCase.parse? arg with
        | some demoCase => printCase demoCase
        | none => throw <| IO.userError usage
  | _ => throw <| IO.userError usage
