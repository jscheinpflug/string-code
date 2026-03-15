import StringCodeLean.BCGhostTyped

namespace StringCodeLean.Examples
open StringCodeLean.BCGhost

abbrev Coord := Nat

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

example : Option.map Kernel.erase (wick (Field.b 0 z) (Field.c 0 w)) =
    some (RawKernel.pole 1 z w 1) := rfl

example : Option.map Kernel.erase (wick (Field.b 1 z) (Field.c 2 w)) =
    some (RawKernel.pole (-6) z w 4) := rfl

example : (normalOrderTwo (Field.c 0 z) (Field.b 0 w)).erase =
    [{ kernel := RawKernel.regular (-1), remainder := [RawField.mk .b 0 w, RawField.mk .c 0 z] }] := rfl

example : (opeField (Field.b 0 z) (NOProd.singleton (Field.c 0 w))).erase =
    [
      { kernel := RawKernel.regular 1, remainder := [RawField.mk .b 0 z, RawField.mk .c 0 w] },
      { kernel := RawKernel.pole 1 z w 1, remainder := [] }
    ] := rfl

example : (opeField (Field.c 0 z) bcAtW).erase =
    [
      { kernel := RawKernel.regular (-1), remainder := [RawField.mk .b 0 w, RawField.mk .c 0 z, RawField.mk .c 0 w] },
      { kernel := RawKernel.pole (-1) w z 1, remainder := [RawField.mk .c 0 w] }
    ] := rfl

example : (ope bbLeft ccRight).erase =
    [
      { kernel := RawKernel.regular 1,
        remainder := [RawField.mk .b 0 z, RawField.mk .b 1 z', RawField.mk .c 0 w, RawField.mk .c 0 w'] },
      { kernel := RawKernel.pole (-1) z w 1,
        remainder := [RawField.mk .b 1 z', RawField.mk .c 0 w'] },
      { kernel := RawKernel.pole 1 z w' 1,
        remainder := [RawField.mk .b 1 z', RawField.mk .c 0 w] },
      { kernel := RawKernel.pole (-1) z' w 2,
        remainder := [RawField.mk .b 0 z, RawField.mk .c 0 w'] },
      { kernel := { coeff := -1, poles := [{ left := z', right := w, order := 2 }, { left := z, right := w', order := 1 }] },
        remainder := [] },
      { kernel := RawKernel.pole 1 z' w' 2,
        remainder := [RawField.mk .b 0 z, RawField.mk .c 0 w] },
      { kernel := { coeff := 1, poles := [{ left := z', right := w', order := 2 }, { left := z, right := w, order := 1 }] },
        remainder := [] }
    ] := rfl

example : normalOrderRaw [RawField.mk .b 0 z, RawField.mk .b 0 z] = Signed.zero := rfl

end StringCodeLean.Examples
