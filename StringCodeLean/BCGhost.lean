namespace StringCodeLean.BCGhost

inductive Chirality where
  | holo
  | anti
  deriving Repr, DecidableEq

inductive Species where
  | b
  | c
  deriving Repr, DecidableEq

namespace Species

def rank : Species → Nat
  | .b => 0
  | .c => 1

end Species

structure RawField (Coord : Type) where
  species : Species
  deriv : Nat
  coord : Coord
  deriving Repr, DecidableEq

namespace RawField

def chirality (_ : RawField Coord) : Chirality := .holo

def ghost : RawField Coord → Int
  | ⟨.b, _, _⟩ => -1
  | ⟨.c, _, _⟩ => 1


def weight : RawField Coord → Int
  | ⟨.b, n, _⟩ => Int.ofNat n + 2
  | ⟨.c, n, _⟩ => Int.ofNat n - 1

variable [Ord Coord]

def compare (lhs rhs : RawField Coord) : Ordering :=
  match Ord.compare lhs.species.rank rhs.species.rank with
  | .eq =>
      match Ord.compare lhs.deriv rhs.deriv with
      | .eq => Ord.compare lhs.coord rhs.coord
      | ord => ord
  | ord => ord

end RawField

structure Field (Coord : Type) (χ : Chirality) (g w : Int) where
  raw : RawField Coord
  hχ : raw.chirality = χ
  hg : raw.ghost = g
  hw : raw.weight = w
  deriving Repr

namespace Field

@[simp] def erase (field : Field Coord χ g w) : RawField Coord := field.raw

@[simp] def b (n : Nat) (coord : Coord) : Field Coord .holo (-1) (Int.ofNat n + 2) where
  raw := ⟨.b, n, coord⟩
  hχ := rfl
  hg := rfl
  hw := rfl

@[simp] def c (n : Nat) (coord : Coord) : Field Coord .holo 1 (Int.ofNat n - 1) where
  raw := ⟨.c, n, coord⟩
  hχ := rfl
  hg := rfl
  hw := rfl

end Field

inductive Sign where
  | pos
  | neg
  deriving Repr, DecidableEq

namespace Sign

def toInt : Sign → Int
  | .pos => 1
  | .neg => -1


def flip : Sign → Sign
  | .pos => .neg
  | .neg => .pos


def mul : Sign → Sign → Sign
  | .pos, s => s
  | .neg, .pos => .neg
  | .neg, .neg => .pos

instance : Mul Sign where
  mul := mul

@[simp] theorem toInt_pos : Sign.toInt .pos = 1 := rfl
@[simp] theorem toInt_neg : Sign.toInt .neg = -1 := rfl
@[simp] theorem toInt_mul (a b : Sign) : (a * b).toInt = a.toInt * b.toInt := by
  cases a <;> cases b <;> rfl

end Sign

inductive Signed (α : Type) where
  | zero
  | nonzero : Sign → α → Signed α
  deriving Repr, DecidableEq

structure PoleFactor (Coord : Type) where
  left : Coord
  right : Coord
  order : Nat
  deriving Repr, DecidableEq


def totalPoleOrder : List (PoleFactor Coord) → Nat
  | [] => 0
  | pole :: poles => pole.order + totalPoleOrder poles

@[simp] theorem totalPoleOrder_append (xs ys : List (PoleFactor Coord)) :
    totalPoleOrder (xs ++ ys) = totalPoleOrder xs + totalPoleOrder ys := by
  induction xs with
  | nil => simp [totalPoleOrder]
  | cons x xs ih => simp [totalPoleOrder, ih, Nat.add_assoc]

structure RawKernel (Coord : Type) where
  coeff : Int
  poles : List (PoleFactor Coord)
  deriving Repr, DecidableEq

namespace RawKernel

@[simp] def regular (coeff : Int) : RawKernel Coord :=
  { coeff, poles := [] }

@[simp] def pole (coeff : Int) (left right : Coord) (order : Nat) : RawKernel Coord :=
  { coeff, poles := [{ left, right, order }] }


def weight (kernel : RawKernel Coord) : Int := Int.ofNat (totalPoleOrder kernel.poles)


def negate (kernel : RawKernel Coord) : RawKernel Coord :=
  { kernel with coeff := -kernel.coeff }


@[inline] def scale (scalar : Int) (kernel : RawKernel Coord) : RawKernel Coord :=
  { kernel with coeff := scalar * kernel.coeff }


@[inline] def mul (lhs rhs : RawKernel Coord) : RawKernel Coord :=
  { coeff := lhs.coeff * rhs.coeff, poles := lhs.poles ++ rhs.poles }

instance : Mul (RawKernel Coord) where
  mul := mul

@[simp] theorem weight_regular (coeff : Int) : (regular (Coord := Coord) coeff).weight = 0 := by
  simp [regular, weight, totalPoleOrder]

@[simp] theorem weight_pole (coeff : Int) (left right : Coord) (order : Nat) :
    (pole (Coord := Coord) coeff left right order).weight = Int.ofNat order := by
  simp [pole, weight, totalPoleOrder]

@[simp] theorem negate_weight (kernel : RawKernel Coord) : kernel.negate.weight = kernel.weight := by
  simp [negate, weight]

@[simp] theorem scale_weight (scalar : Int) (kernel : RawKernel Coord) : (kernel.scale scalar).weight = kernel.weight := by
  simp [scale, weight]

@[simp] theorem mul_weight (lhs rhs : RawKernel Coord) : (lhs * rhs).weight = lhs.weight + rhs.weight := by
  cases lhs with
  | mk lcoeff lpoles =>
    cases rhs with
    | mk rcoeff rpoles =>
      change Int.ofNat (totalPoleOrder (lpoles ++ rpoles)) = Int.ofNat (totalPoleOrder lpoles) + Int.ofNat (totalPoleOrder rpoles)
      rw [totalPoleOrder_append]
      simp

end RawKernel

structure Kernel (Coord : Type) (w : Int) where
  raw : RawKernel Coord
  hw : raw.weight = w
  deriving Repr

namespace Kernel

@[simp] def erase (kernel : Kernel Coord w) : RawKernel Coord := kernel.raw

@[simp] def regular (coeff : Int) : Kernel Coord 0 where
  raw := RawKernel.regular coeff
  hw := by simp [RawKernel.regular, RawKernel.weight, totalPoleOrder]

@[simp] def pole (coeff : Int) (left right : Coord) (order : Nat) : Kernel Coord (Int.ofNat order) where
  raw := RawKernel.pole coeff left right order
  hw := by simp [RawKernel.pole, RawKernel.weight, totalPoleOrder]

@[simp] def scale (scalar : Int) (kernel : Kernel Coord w) : Kernel Coord w where
  raw := kernel.raw.scale scalar
  hw := by simpa using kernel.hw

@[simp] def mul (lhs : Kernel Coord w₁) (rhs : Kernel Coord w₂) : Kernel Coord (w₁ + w₂) where
  raw := lhs.raw * rhs.raw
  hw := by
    rw [RawKernel.mul_weight, lhs.hw, rhs.hw]

end Kernel

structure RawTerm (Coord : Type) where
  kernel : RawKernel Coord
  remainder : List (RawField Coord)
  deriving Repr, DecidableEq

namespace RawTerm

def prepend (field : RawField Coord) (term : RawTerm Coord) : RawTerm Coord :=
  { term with remainder := field :: term.remainder }


def negate (term : RawTerm Coord) : RawTerm Coord :=
  { term with kernel := term.kernel.negate }

@[simp] def scale (scalar : Int) (term : RawTerm Coord) : RawTerm Coord :=
  { term with kernel := term.kernel.scale scalar }

@[simp] def mulKernel (kernel : RawKernel Coord) (term : RawTerm Coord) : RawTerm Coord :=
  { kernel := kernel * term.kernel, remainder := term.remainder }

end RawTerm


def totalBy (grade : RawField Coord → Int) : List (RawField Coord) → Int
  | [] => 0
  | field :: tail => grade field + totalBy grade tail

@[simp] theorem totalBy_append (grade : RawField Coord → Int) (xs ys : List (RawField Coord)) :
    totalBy grade (xs ++ ys) = totalBy grade xs + totalBy grade ys := by
  induction xs with
  | nil => simp [totalBy]
  | cons x xs ih => simp [totalBy, ih, Int.add_assoc]

@[simp] theorem totalBy_reverse (grade : RawField Coord → Int) (xs : List (RawField Coord)) :
    totalBy grade xs.reverse = totalBy grade xs := by
  induction xs with
  | nil => simp [totalBy]
  | cons x xs ih =>
      simp [List.reverse_cons, totalBy_append, totalBy, ih]
      omega

def totalGhost : List (RawField Coord) → Int := totalBy RawField.ghost
def totalWeight : List (RawField Coord) → Int := totalBy RawField.weight

@[simp] theorem totalGhost_append (xs ys : List (RawField Coord)) :
    totalGhost (xs ++ ys) = totalGhost xs + totalGhost ys := totalBy_append RawField.ghost xs ys

@[simp] theorem totalGhost_reverse (xs : List (RawField Coord)) :
    totalGhost xs.reverse = totalGhost xs := totalBy_reverse RawField.ghost xs

@[simp] theorem totalWeight_append (xs ys : List (RawField Coord)) :
    totalWeight (xs ++ ys) = totalWeight xs + totalWeight ys := totalBy_append RawField.weight xs ys

@[simp] theorem totalWeight_reverse (xs : List (RawField Coord)) :
    totalWeight xs.reverse = totalWeight xs := totalBy_reverse RawField.weight xs

namespace RawTerm

@[simp] def ghost (term : RawTerm Coord) : Int := totalGhost term.remainder
@[simp] def weight (term : RawTerm Coord) : Int := term.kernel.weight + totalWeight term.remainder

def grade (kernelGrade : RawKernel Coord → Int) (fieldGrade : RawField Coord → Int) (term : RawTerm Coord) : Int :=
  kernelGrade term.kernel + totalBy fieldGrade term.remainder

@[simp] theorem grade_ghost (term : RawTerm Coord) :
    term.grade (fun _ => 0) RawField.ghost = term.ghost := by
  simp [RawTerm.grade, RawTerm.ghost, totalGhost]

@[simp] theorem grade_weight (term : RawTerm Coord) :
    term.grade RawKernel.weight RawField.weight = term.weight := by
  simp [RawTerm.grade, RawTerm.weight, totalWeight]

@[simp] theorem scale_ghost (scalar : Int) (term : RawTerm Coord) :
    (term.scale scalar).ghost = term.ghost := rfl

@[simp] theorem scale_weight (scalar : Int) (term : RawTerm Coord) :
    (term.scale scalar).weight = term.weight := by
  simp [RawTerm.weight, RawKernel.scale_weight]

end RawTerm

structure NOProd (Coord : Type) (χ : Chirality) (g w : Int) where
  fields : List (RawField Coord)
  hχ : ∀ field ∈ fields, field.chirality = χ
  hg : totalGhost fields = g
  hw : totalWeight fields = w
  deriving Repr

namespace NOProd

@[simp] def erase (prod : NOProd Coord χ g w) : List (RawField Coord) := prod.fields

@[simp] def nil : NOProd Coord .holo 0 0 where
  fields := []
  hχ := by intro field h; cases h
  hg := rfl
  hw := rfl

@[simp] def singleton (field : Field Coord .holo g w) : NOProd Coord .holo g w where
  fields := [field.raw]
  hχ := by
    intro f hf
    simp at hf
    rcases hf with rfl
    simpa using field.hχ
  hg := by simpa [totalGhost, totalBy] using field.hg
  hw := by simpa [totalWeight, totalBy] using field.hw

@[simp] def ofRawHolo (fields : List (RawField Coord)) : NOProd Coord .holo (totalGhost fields) (totalWeight fields) where
  fields := fields
  hχ := by intro field hf; simp [RawField.chirality]
  hg := rfl
  hw := rfl

end NOProd

structure Expr (Coord : Type) (χ : Chirality) (g w : Int) where
  terms : List (RawTerm Coord)
  hχ : ∀ term ∈ terms, ∀ field ∈ term.remainder, field.chirality = χ
  hg : ∀ term ∈ terms, term.ghost = g
  hw : ∀ term ∈ terms, term.weight = w
  deriving Repr

namespace Expr

@[simp] def erase (expr : Expr Coord χ g w) : List (RawTerm Coord) := expr.terms

@[simp] def zero : Expr Coord χ g w where
  terms := []
  hχ := by intro term h; cases h
  hg := by intro term h; cases h
  hw := by intro term h; cases h

instance : Zero (Expr Coord χ g w) where
  zero := zero

@[simp] def add (lhs rhs : Expr Coord χ g w) : Expr Coord χ g w where
  terms := lhs.terms ++ rhs.terms
  hχ := by
    intro term hTerm field hField
    simp at hTerm
    rcases hTerm with hTerm | hTerm
    · exact lhs.hχ term hTerm field hField
    · exact rhs.hχ term hTerm field hField
  hg := by
    intro term hTerm
    simp at hTerm
    rcases hTerm with hTerm | hTerm
    · exact lhs.hg term hTerm
    · exact rhs.hg term hTerm
  hw := by
    intro term hTerm
    simp at hTerm
    rcases hTerm with hTerm | hTerm
    · exact lhs.hw term hTerm
    · exact rhs.hw term hTerm

instance : Add (Expr Coord χ g w) where
  add := add

@[simp] def scale (scalar : Int) (expr : Expr Coord χ g w) : Expr Coord χ g w where
  terms := expr.terms.map (RawTerm.scale scalar)
  hχ := by
    intro term hTerm field hField
    simp at hTerm
    rcases hTerm with ⟨base, hBase, rfl⟩
    exact expr.hχ base hBase field hField
  hg := by
    intro term hTerm
    simp at hTerm
    rcases hTerm with ⟨base, hBase, rfl⟩
    simpa using expr.hg base hBase
  hw := by
    intro term hTerm
    simp at hTerm
    rcases hTerm with ⟨base, hBase, rfl⟩
    simpa using expr.hw base hBase

instance : SMul Int (Expr Coord χ g w) where
  smul := scale

@[simp] theorem zero_erase : (0 : Expr Coord χ g w).erase = [] := rfl

@[simp] theorem add_erase (lhs rhs : Expr Coord χ g w) :
    (lhs + rhs).erase = lhs.erase ++ rhs.erase := rfl

@[simp] theorem smul_erase (scalar : Int) (expr : Expr Coord χ g w) :
    (scalar • expr).erase = expr.erase.map (RawTerm.scale scalar) := rfl

def Eqv (lhs rhs : Expr Coord χ g w) : Prop :=
  List.Perm lhs.terms rhs.terms

@[refl] theorem eqv_refl (expr : Expr Coord χ g w) : expr.Eqv expr := List.Perm.refl _

@[symm] theorem eqv_symm {lhs rhs : Expr Coord χ g w} :
    lhs.Eqv rhs → rhs.Eqv lhs := List.Perm.symm

theorem eqv_trans {lhs mid rhs : Expr Coord χ g w} :
    lhs.Eqv mid → mid.Eqv rhs → lhs.Eqv rhs := List.Perm.trans

@[simp] theorem eqv_erase {lhs rhs : Expr Coord χ g w} :
    lhs.Eqv rhs ↔ List.Perm lhs.erase rhs.erase := Iff.rfl

@[ext] theorem ext
    {lhs rhs : Expr Coord χ g w}
    (hTerms : lhs.terms = rhs.terms) :
    lhs = rhs := by
  cases lhs
  cases rhs
  cases hTerms
  simp

end Expr

namespace NOProd

@[simp] def toExpr (prod : NOProd Coord χ g w) : Expr Coord χ g w where
  terms := [{ kernel := RawKernel.regular 1, remainder := prod.fields }]
  hχ := by
    intro term hTerm field hField
    simp at hTerm
    rcases hTerm with rfl
    exact prod.hχ field hField
  hg := by
    intro term hTerm
    simp at hTerm
    rcases hTerm with rfl
    simpa [RawTerm.ghost] using prod.hg
  hw := by
    intro term hTerm
    simp at hTerm
    rcases hTerm with rfl
    simpa [RawTerm.weight, RawKernel.weight, totalPoleOrder] using prod.hw

@[simp] theorem toExpr_erase (prod : NOProd Coord χ g w) :
    prod.toExpr.erase = [{ kernel := RawKernel.regular 1, remainder := prod.fields }] := rfl

end NOProd


def natFactorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * natFactorial n


def signPow (n : Nat) : Int :=
  if n % 2 = 0 then 1 else -1


def wickCoeff (n m : Nat) : Int :=
  signPow n * Int.ofNat (natFactorial (n + m))


@[inline] def wickRaw (lhs rhs : RawField Coord) : Option (RawKernel Coord) :=
  match lhs, rhs with
  | ⟨.b, n, z⟩, ⟨.c, m, w⟩ => some (RawKernel.pole (wickCoeff n m) z w (n + m + 1))
  | ⟨.c, m, w⟩, ⟨.b, n, z⟩ => some (RawKernel.pole (-(wickCoeff n m)) z w (n + m + 1))
  | _, _ => none

variable [Ord Coord]


@[inline] def insertRaw (field : RawField Coord) : List (RawField Coord) → Signed (List (RawField Coord))
  | [] => .nonzero .pos [field]
  | head :: tail =>
      match RawField.compare field head with
      | .lt => .nonzero .pos (field :: head :: tail)
      | .eq => .zero
      | .gt =>
          match insertRaw field tail with
          | .zero => .zero
          | .nonzero sign rest => .nonzero sign.flip (head :: rest)


def normalOrderRaw : List (RawField Coord) → Signed (List (RawField Coord))
  | [] => .nonzero .pos []
  | field :: tail =>
      match normalOrderRaw tail with
      | .zero => .zero
      | .nonzero sign orderedTail =>
          match insertRaw field orderedTail with
          | .zero => .zero
          | .nonzero sign' ordered => .nonzero (sign * sign') ordered

@[inline] def regularInsertTermRaw (lhs : RawField Coord) (base : RawTerm Coord) : List (RawTerm Coord) :=
  match insertRaw lhs base.remainder with
  | .zero => []
  | .nonzero sign ordered => [{ kernel := base.kernel.scale sign.toInt, remainder := ordered }]

@[inline] def contractTermsRawGo
    (lhs : RawField Coord) (baseKernel : RawKernel Coord)
    (prefixRev : List (RawField Coord)) (sign : Sign) :
    List (RawField Coord) → List (RawTerm Coord)
  | [] => []
  | head :: tail =>
      let current :=
        match wickRaw lhs head with
        | none => []
        | some kernel =>
            [{ kernel := (baseKernel * kernel).scale sign.toInt
             , remainder := prefixRev.reverse ++ tail }]
      current ++ contractTermsRawGo lhs baseKernel (head :: prefixRev) sign.flip tail

@[inline] def contractTermsRaw (lhs : RawField Coord) (baseKernel : RawKernel Coord) :
    List (RawField Coord) → List (RawTerm Coord) :=
  contractTermsRawGo lhs baseKernel [] .pos
@[inline] def actFieldOnTermRaw (lhs : RawField Coord) (base : RawTerm Coord) : List (RawTerm Coord) :=
  regularInsertTermRaw lhs base ++ contractTermsRaw lhs base.kernel base.remainder
@[inline] def applyFieldOnTermsRaw (lhs : RawField Coord) :
    List (RawTerm Coord) → List (RawTerm Coord)
  | [] => []
  | base :: bases => actFieldOnTermRaw lhs base ++ applyFieldOnTermsRaw lhs bases
@[inline] def contractTermsRawArrayAcc
    (lhs : RawField Coord) (baseKernel : RawKernel Coord)
    (prefixRev : List (RawField Coord)) (sign : Sign) :
    List (RawField Coord) → Array (RawTerm Coord) → Array (RawTerm Coord)
  | [], acc => acc
  | head :: tail, acc =>
      let acc :=
        match wickRaw lhs head with
        | none => acc
        | some kernel =>
            acc.push
              { kernel := (baseKernel * kernel).scale sign.toInt
              , remainder := prefixRev.reverse ++ tail }
      contractTermsRawArrayAcc lhs baseKernel (head :: prefixRev) sign.flip tail acc
@[inline] def contractTermsRawFast
    (lhs : RawField Coord) (baseKernel : RawKernel Coord) (rhs : List (RawField Coord)) :
    List (RawTerm Coord) :=
  (contractTermsRawArrayAcc lhs baseKernel [] .pos rhs #[]).toList
@[inline] def actFieldOnTermRawArrayAcc
    (lhs : RawField Coord) (base : RawTerm Coord) (acc : Array (RawTerm Coord)) :
    Array (RawTerm Coord) :=
  let acc :=
    match insertRaw lhs base.remainder with
    | .zero => acc
    | .nonzero sign ordered =>
        acc.push { kernel := base.kernel.scale sign.toInt, remainder := ordered }
  contractTermsRawArrayAcc lhs base.kernel [] .pos base.remainder acc
@[inline] def applyFieldOnTermsRawArrayAcc
    (lhs : RawField Coord) :
    List (RawTerm Coord) → Array (RawTerm Coord) → Array (RawTerm Coord)
  | [], acc => acc
  | base :: bases, acc =>
      applyFieldOnTermsRawArrayAcc lhs bases (actFieldOnTermRawArrayAcc lhs base acc)
@[inline] def applyFieldOnTermsRawFast (lhs : RawField Coord) (bases : List (RawTerm Coord)) :
    List (RawTerm Coord) :=
  (applyFieldOnTermsRawArrayAcc lhs bases #[]).toList
@[inline] def opeRaw : List (RawField Coord) → List (RawField Coord) → List (RawTerm Coord)
  | [], rhs => [{ kernel := RawKernel.regular 1, remainder := rhs }]
  | head :: tail, rhs => applyFieldOnTermsRaw head (opeRaw tail rhs)

@[inline] def opeRawFast : List (RawField Coord) → List (RawField Coord) → List (RawTerm Coord)
  | [], rhs => [{ kernel := RawKernel.regular 1, remainder := rhs }]
  | head :: tail, rhs => applyFieldOnTermsRawFast head (opeRawFast tail rhs)
@[inline] def mulKernelTermsRaw (kernel : RawKernel Coord) : List (RawTerm Coord) → List (RawTerm Coord)
  | [] => []
  | term :: terms => term.mulKernel kernel :: mulKernelTermsRaw kernel terms

omit [Ord Coord] in
@[inline] def opeTermRaw (lhs rhs : RawTerm Coord) : List (RawTerm Coord) :=
  mulKernelTermsRaw (lhs.kernel * rhs.kernel) (opeRaw lhs.remainder rhs.remainder)

@[inline] def applyTermOnTermsRaw (lhs : RawTerm Coord) : List (RawTerm Coord) → List (RawTerm Coord)
  | [] => []
  | rhs :: rhss => opeTermRaw lhs rhs ++ applyTermOnTermsRaw lhs rhss

@[inline] def opeExprRaw : List (RawTerm Coord) → List (RawTerm Coord) → List (RawTerm Coord)
  | [], _ => []
  | lhs :: lhss, rhs => applyTermOnTermsRaw lhs rhs ++ opeExprRaw lhss rhs
end StringCodeLean.BCGhost
