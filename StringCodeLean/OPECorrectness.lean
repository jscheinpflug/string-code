import StringCodeLean.BCGhostTyped
import StringCodeLean.Correctness

namespace StringCodeLean.BCGhost

namespace RawKernel

@[simp] theorem regular_one_mul (kernel : RawKernel Coord) :
    RawKernel.regular 1 * kernel = kernel := by
  cases kernel with
  | mk coeff poles =>
      change RawKernel.mul (RawKernel.regular 1) { coeff := coeff, poles := poles } =
        ({ coeff := coeff, poles := poles } : RawKernel Coord)
      simp [RawKernel.mul, RawKernel.regular]

@[simp] theorem mul_regular_one (kernel : RawKernel Coord) :
    kernel * RawKernel.regular 1 = kernel := by
  cases kernel with
  | mk coeff poles =>
      change RawKernel.mul { coeff := coeff, poles := poles } (RawKernel.regular 1) =
        ({ coeff := coeff, poles := poles } : RawKernel Coord)
      simp [RawKernel.mul, RawKernel.regular]

@[simp] theorem scale_mul (scalar : Int) (lhs rhs : RawKernel Coord) :
    lhs.scale scalar * rhs = (lhs * rhs).scale scalar := by
  cases lhs with
  | mk lcoeff lpoles =>
    cases rhs with
    | mk rcoeff rpoles =>
      change RawKernel.mul { coeff := scalar * lcoeff, poles := lpoles } { coeff := rcoeff, poles := rpoles } =
        RawKernel.scale scalar (RawKernel.mul { coeff := lcoeff, poles := lpoles } { coeff := rcoeff, poles := rpoles })
      simp [RawKernel.scale, RawKernel.mul, Int.mul_assoc]

@[simp] theorem mul_scale (scalar : Int) (lhs rhs : RawKernel Coord) :
    lhs * rhs.scale scalar = (lhs * rhs).scale scalar := by
  cases lhs with
  | mk lcoeff lpoles =>
    cases rhs with
    | mk rcoeff rpoles =>
      change RawKernel.mul { coeff := lcoeff, poles := lpoles } { coeff := scalar * rcoeff, poles := rpoles } =
        RawKernel.scale scalar (RawKernel.mul { coeff := lcoeff, poles := lpoles } { coeff := rcoeff, poles := rpoles })
      simp [RawKernel.scale, RawKernel.mul, Int.mul_left_comm]

end RawKernel

namespace RawTerm

@[simp] theorem scale_remainder (scalar : Int) (term : RawTerm Coord) :
    (term.scale scalar).remainder = term.remainder := rfl

@[simp] theorem mulKernel_remainder (kernel : RawKernel Coord) (term : RawTerm Coord) :
    (term.mulKernel kernel).remainder = term.remainder := rfl

@[simp] theorem mulKernel_regular_one (term : RawTerm Coord) :
    term.mulKernel (RawKernel.regular 1) = term := by
  cases term with
  | mk kernel remainder =>
      change
        ({ kernel := RawKernel.mul (RawKernel.regular 1) kernel, remainder := remainder } : RawTerm Coord) =
          { kernel := kernel, remainder := remainder }
      simp [RawKernel.regular, RawKernel.mul]

@[simp] theorem mulKernel_scaleKernel (scalar : Int) (kernel : RawKernel Coord) (term : RawTerm Coord) :
    term.mulKernel (kernel.scale scalar) = (term.mulKernel kernel).scale scalar := by
  cases term with
  | mk termKernel remainder =>
      cases kernel with
      | mk coeff poles =>
          change
            ({ kernel := RawKernel.mul { coeff := scalar * coeff, poles := poles } termKernel, remainder := remainder } :
              RawTerm Coord) =
              { kernel := RawKernel.scale scalar (RawKernel.mul { coeff := coeff, poles := poles } termKernel)
              , remainder := remainder }
          simp [RawKernel.scale, RawKernel.mul, Int.mul_assoc]

@[simp] theorem mulKernel_ghost (kernel : RawKernel Coord) (term : RawTerm Coord) :
    (term.mulKernel kernel).ghost = term.ghost := rfl

@[simp] theorem mulKernel_weight (kernel : RawKernel Coord) (term : RawTerm Coord) :
    (term.mulKernel kernel).weight = kernel.weight + term.weight := by
  simp [RawTerm.weight, Int.add_assoc]

end RawTerm

section ExprOrdered

variable {Coord : Type} [Ord Coord]

omit [Ord Coord] in
@[simp] theorem mem_mulKernelTermsRaw
    {kernel : RawKernel Coord} {terms : List (RawTerm Coord)} {term : RawTerm Coord} :
    term ∈ mulKernelTermsRaw kernel terms ↔ ∃ base ∈ terms, term = base.mulKernel kernel := by
  induction terms with
  | nil =>
      simp [mulKernelTermsRaw]
  | cons base terms ih =>
      simp [mulKernelTermsRaw, ih]

omit [Ord Coord] in
@[simp] theorem mulKernelTermsRaw_append
    (kernel : RawKernel Coord) (terms₁ terms₂ : List (RawTerm Coord)) :
    mulKernelTermsRaw kernel (terms₁ ++ terms₂) =
      mulKernelTermsRaw kernel terms₁ ++ mulKernelTermsRaw kernel terms₂ := by
  induction terms₁ with
  | nil =>
      simp [mulKernelTermsRaw]
  | cons term terms ih =>
      simp [mulKernelTermsRaw, ih]

omit [Ord Coord] in
@[simp] theorem mulKernelTermsRaw_regular_one
    (terms : List (RawTerm Coord)) :
    mulKernelTermsRaw (RawKernel.regular 1) terms = terms := by
  induction terms with
  | nil =>
      simp [mulKernelTermsRaw]
  | cons term terms ih =>
      simp [mulKernelTermsRaw]
      constructor
      · cases term with
        | mk kernel remainder =>
            simpa using (RawKernel.regular_one_mul kernel)
      · simpa [RawKernel.regular] using ih

omit [Ord Coord] in
@[simp] theorem mulKernelTermsRaw_scaleKernel
    (scalar : Int) (kernel : RawKernel Coord) (terms : List (RawTerm Coord)) :
    mulKernelTermsRaw (kernel.scale scalar) terms =
      (mulKernelTermsRaw kernel terms).map (RawTerm.scale scalar) := by
  induction terms with
  | nil =>
      simp [mulKernelTermsRaw]
  | cons term terms ih =>
      simp [mulKernelTermsRaw, ih]

@[simp] theorem opeTermRaw_term_ghost
    {lhs rhs : RawTerm Coord} {term : RawTerm Coord}
    (h : term ∈ opeTermRaw lhs rhs) :
    term.ghost = lhs.ghost + rhs.ghost := by
  unfold opeTermRaw at h
  rcases (mem_mulKernelTermsRaw.mp h) with ⟨base, hBase, rfl⟩
  have hGhost := opeRaw_term_ghost (lhs := lhs.remainder) (rhs := rhs.remainder) (term := base) hBase
  simp [RawTerm.ghost] at hGhost ⊢
  omega

@[simp] theorem opeTermRaw_term_weight
    {lhs rhs : RawTerm Coord} {term : RawTerm Coord}
    (h : term ∈ opeTermRaw lhs rhs) :
    term.weight = lhs.weight + rhs.weight := by
  unfold opeTermRaw at h
  rcases (mem_mulKernelTermsRaw.mp h) with ⟨base, hBase, rfl⟩
  have hWeight := opeRaw_term_weight (lhs := lhs.remainder) (rhs := rhs.remainder) (term := base) hBase
  simp [RawTerm.weight, Int.add_assoc, Int.add_left_comm, Int.add_comm] at hWeight ⊢
  omega

@[simp] theorem opeTermRaw_scale_left
    (scalar : Int) (lhs rhs : RawTerm Coord) :
    opeTermRaw (lhs.scale scalar) rhs = (opeTermRaw lhs rhs).map (RawTerm.scale scalar) := by
  simp [opeTermRaw, RawTerm.scale]

@[simp] theorem opeTermRaw_scale_right
    (scalar : Int) (lhs rhs : RawTerm Coord) :
    opeTermRaw lhs (rhs.scale scalar) = (opeTermRaw lhs rhs).map (RawTerm.scale scalar) := by
  simp [opeTermRaw, RawTerm.scale]

@[simp] theorem applyTermOnTermsRaw_append
    (lhs : RawTerm Coord) (rhs₁ rhs₂ : List (RawTerm Coord)) :
    applyTermOnTermsRaw lhs (rhs₁ ++ rhs₂) =
      applyTermOnTermsRaw lhs rhs₁ ++ applyTermOnTermsRaw lhs rhs₂ := by
  induction rhs₁ with
  | nil =>
      simp [applyTermOnTermsRaw]
  | cons rhs rhss ih =>
      simp [applyTermOnTermsRaw, ih, List.append_assoc]

@[simp] theorem applyTermOnTermsRaw_term_ghost
    {lhs : RawTerm Coord} {bases : List (RawTerm Coord)}
    (hBases : ∀ base ∈ bases, base.ghost = g) :
    ∀ {term : RawTerm Coord}, term ∈ applyTermOnTermsRaw lhs bases → term.ghost = lhs.ghost + g
  | term, h => by
      induction bases generalizing term with
      | nil =>
          cases h
      | cons base bases ih =>
          simp [applyTermOnTermsRaw] at h
          rcases h with h | h
          · have hGhost := opeTermRaw_term_ghost (lhs := lhs) (rhs := base) (term := term) h
            rw [hBases base (by simp)] at hGhost
            simpa using hGhost
          · have hBases' : ∀ base' ∈ bases, base'.ghost = g := by
              intro base' hBase'
              exact hBases base' (by simp [hBase'])
            exact ih (term := term) hBases' h

@[simp] theorem applyTermOnTermsRaw_term_weight
    {lhs : RawTerm Coord} {bases : List (RawTerm Coord)}
    (hBases : ∀ base ∈ bases, base.weight = w) :
    ∀ {term : RawTerm Coord}, term ∈ applyTermOnTermsRaw lhs bases → term.weight = lhs.weight + w
  | term, h => by
      induction bases generalizing term with
      | nil =>
          cases h
      | cons base bases ih =>
          simp [applyTermOnTermsRaw] at h
          rcases h with h | h
          · have hWeight := opeTermRaw_term_weight (lhs := lhs) (rhs := base) (term := term) h
            rw [hBases base (by simp)] at hWeight
            simpa using hWeight
          · have hBases' : ∀ base' ∈ bases, base'.weight = w := by
              intro base' hBase'
              exact hBases base' (by simp [hBase'])
            exact ih (term := term) hBases' h

@[simp] theorem applyTermOnTermsRaw_scale_left
    (scalar : Int) (lhs : RawTerm Coord) (bases : List (RawTerm Coord)) :
    applyTermOnTermsRaw (lhs.scale scalar) bases =
      (applyTermOnTermsRaw lhs bases).map (RawTerm.scale scalar) := by
  induction bases with
  | nil =>
      simp [applyTermOnTermsRaw]
  | cons base bases ih =>
      calc
        applyTermOnTermsRaw (lhs.scale scalar) (base :: bases)
            = opeTermRaw (lhs.scale scalar) base ++ applyTermOnTermsRaw (lhs.scale scalar) bases := by
                simp [applyTermOnTermsRaw]
        _ = (opeTermRaw lhs base).map (RawTerm.scale scalar) ++
              (applyTermOnTermsRaw lhs bases).map (RawTerm.scale scalar) := by
                rw [opeTermRaw_scale_left, ih]
        _ = (applyTermOnTermsRaw lhs (base :: bases)).map (RawTerm.scale scalar) := by
              simp [applyTermOnTermsRaw, List.map_append]

@[simp] theorem applyTermOnTermsRaw_scale_right
    (scalar : Int) (lhs : RawTerm Coord) (bases : List (RawTerm Coord)) :
    applyTermOnTermsRaw lhs (bases.map (RawTerm.scale scalar)) =
      (applyTermOnTermsRaw lhs bases).map (RawTerm.scale scalar) := by
  induction bases with
  | nil =>
      simp [applyTermOnTermsRaw]
  | cons base bases ih =>
      calc
        applyTermOnTermsRaw lhs ((base :: bases).map (RawTerm.scale scalar))
            = opeTermRaw lhs (base.scale scalar) ++ applyTermOnTermsRaw lhs (bases.map (RawTerm.scale scalar)) := by
                simp [applyTermOnTermsRaw]
        _ = (opeTermRaw lhs base).map (RawTerm.scale scalar) ++
              (applyTermOnTermsRaw lhs bases).map (RawTerm.scale scalar) := by
                rw [opeTermRaw_scale_right, ih]
        _ = (applyTermOnTermsRaw lhs (base :: bases)).map (RawTerm.scale scalar) := by
              simp [applyTermOnTermsRaw, List.map_append]

@[simp] theorem opeExprRaw_append_left
    (lhs₁ lhs₂ rhs : List (RawTerm Coord)) :
    opeExprRaw (lhs₁ ++ lhs₂) rhs = opeExprRaw lhs₁ rhs ++ opeExprRaw lhs₂ rhs := by
  induction lhs₁ with
  | nil =>
      simp [opeExprRaw]
  | cons lhs lhss ih =>
      simp [opeExprRaw, ih, List.append_assoc]

theorem opeExprRaw_append_right_perm
    (lhs rhs₁ rhs₂ : List (RawTerm Coord)) :
    List.Perm (opeExprRaw lhs (rhs₁ ++ rhs₂)) (opeExprRaw lhs rhs₁ ++ opeExprRaw lhs rhs₂) := by
  induction lhs with
  | nil =>
      simp [opeExprRaw]
  | cons term terms ih =>
      let a := applyTermOnTermsRaw term rhs₁
      let b := applyTermOnTermsRaw term rhs₂
      let c := opeExprRaw terms rhs₁
      let d := opeExprRaw terms rhs₂
      have hTail : List.Perm ((a ++ b) ++ opeExprRaw terms (rhs₁ ++ rhs₂)) ((a ++ b) ++ (c ++ d)) := by
        simpa [a, b, c, d] using ih.append_left (a ++ b)
      have hSwap : List.Perm ((a ++ b) ++ (c ++ d)) ((a ++ c) ++ (b ++ d)) := by
        simpa [a, b, c, d, List.append_assoc] using
          (List.perm_append_comm_assoc b c d).append_left a
      refine (by simpa [opeExprRaw, applyTermOnTermsRaw_append, a, b, c, d, List.append_assoc] using hTail.trans hSwap)

@[simp] theorem opeExprRaw_scale_left
    (scalar : Int) (lhs rhs : List (RawTerm Coord)) :
    opeExprRaw (lhs.map (RawTerm.scale scalar)) rhs =
      (opeExprRaw lhs rhs).map (RawTerm.scale scalar) := by
  induction lhs with
  | nil =>
      simp [opeExprRaw]
  | cons term terms ih =>
      calc
        opeExprRaw ((term :: terms).map (RawTerm.scale scalar)) rhs
            = applyTermOnTermsRaw (term.scale scalar) rhs ++ opeExprRaw (terms.map (RawTerm.scale scalar)) rhs := by
                simp [opeExprRaw]
        _ = (applyTermOnTermsRaw term rhs).map (RawTerm.scale scalar) ++
              (opeExprRaw terms rhs).map (RawTerm.scale scalar) := by
                rw [applyTermOnTermsRaw_scale_left, ih]
        _ = (opeExprRaw (term :: terms) rhs).map (RawTerm.scale scalar) := by
              simp [opeExprRaw, List.map_append]

@[simp] theorem opeExprRaw_scale_right
    (scalar : Int) (lhs rhs : List (RawTerm Coord)) :
    opeExprRaw lhs (rhs.map (RawTerm.scale scalar)) =
      (opeExprRaw lhs rhs).map (RawTerm.scale scalar) := by
  induction lhs with
  | nil =>
      simp [opeExprRaw]
  | cons term terms ih =>
      calc
        opeExprRaw (term :: terms) (rhs.map (RawTerm.scale scalar))
            = applyTermOnTermsRaw term (rhs.map (RawTerm.scale scalar)) ++
              opeExprRaw terms (rhs.map (RawTerm.scale scalar)) := by
                simp [opeExprRaw]
        _ = (applyTermOnTermsRaw term rhs).map (RawTerm.scale scalar) ++
              (opeExprRaw terms rhs).map (RawTerm.scale scalar) := by
                rw [applyTermOnTermsRaw_scale_right, ih]
        _ = (opeExprRaw (term :: terms) rhs).map (RawTerm.scale scalar) := by
              simp [opeExprRaw, List.map_append]

@[simp] theorem opeExprRaw_term_ghost
    {lhss rhss : List (RawTerm Coord)}
    (hLhs : ∀ lhs ∈ lhss, lhs.ghost = g₁)
    (hRhs : ∀ rhs ∈ rhss, rhs.ghost = g₂) :
    ∀ {term : RawTerm Coord}, term ∈ opeExprRaw lhss rhss → term.ghost = g₁ + g₂
  | term, h => by
      induction lhss generalizing term with
      | nil =>
          cases h
      | cons lhs lhss ih =>
          simp [opeExprRaw] at h
          rcases h with h | h
          · have hGhost :=
              applyTermOnTermsRaw_term_ghost (lhs := lhs) (bases := rhss) (g := g₂) hRhs h
            rw [hLhs lhs (by simp)] at hGhost
            simpa [Int.add_comm] using hGhost
          · have hLhs' : ∀ lhs' ∈ lhss, lhs'.ghost = g₁ := by
              intro lhs' hLhs'
              exact hLhs lhs' (by simp [hLhs'])
            exact ih (term := term) hLhs' h

@[simp] theorem opeExprRaw_term_weight
    {lhss rhss : List (RawTerm Coord)}
    (hLhs : ∀ lhs ∈ lhss, lhs.weight = w₁)
    (hRhs : ∀ rhs ∈ rhss, rhs.weight = w₂) :
    ∀ {term : RawTerm Coord}, term ∈ opeExprRaw lhss rhss → term.weight = w₁ + w₂
  | term, h => by
      induction lhss generalizing term with
      | nil =>
          cases h
      | cons lhs lhss ih =>
          simp [opeExprRaw] at h
          rcases h with h | h
          · have hWeight :=
              applyTermOnTermsRaw_term_weight (lhs := lhs) (bases := rhss) (w := w₂) hRhs h
            rw [hLhs lhs (by simp)] at hWeight
            simpa [Int.add_comm] using hWeight
          · have hLhs' : ∀ lhs' ∈ lhss, lhs'.weight = w₁ := by
              intro lhs' hLhs'
              exact hLhs lhs' (by simp [hLhs'])
            exact ih (term := term) hLhs' h

def opeExpr
    (lhs : Expr Coord .holo g₁ w₁) (rhs : Expr Coord .holo g₂ w₂) :
    Expr Coord .holo (g₁ + g₂) (w₁ + w₂) where
  terms := opeExprRaw lhs.terms rhs.terms
  hχ := by
    intro term hTerm field hField
    simp [RawField.chirality]
  hg := by
    intro term hTerm
    exact opeExprRaw_term_ghost lhs.hg rhs.hg hTerm
  hw := by
    intro term hTerm
    exact opeExprRaw_term_weight lhs.hw rhs.hw hTerm

@[simp] theorem opeExpr_erase
    (lhs : Expr Coord .holo g₁ w₁) (rhs : Expr Coord .holo g₂ w₂) :
    (opeExpr lhs rhs).erase = opeExprRaw lhs.terms rhs.terms := rfl

@[simp] theorem opeExpr_toExpr
    (lhs : NOProd Coord .holo g₁ w₁) (rhs : NOProd Coord .holo g₂ w₂) :
    opeExpr lhs.toExpr rhs.toExpr = ope lhs rhs := by
  apply Expr.ext
  calc
    (opeExpr lhs.toExpr rhs.toExpr).terms
        = opeExprRaw lhs.toExpr.terms rhs.toExpr.terms := rfl
    _ = opeRaw lhs.fields rhs.fields := by
          simpa [opeExprRaw, applyTermOnTermsRaw, opeTermRaw] using
            (show
              mulKernelTermsRaw (((RawKernel.regular 1 : RawKernel Coord) * RawKernel.regular 1))
                (opeRaw lhs.fields rhs.fields) = opeRaw lhs.fields rhs.fields from by
                have hRegMul :
                    ((RawKernel.regular 1 : RawKernel Coord) * RawKernel.regular 1) = RawKernel.regular 1 := by
                  change RawKernel.mul (RawKernel.regular 1) (RawKernel.regular 1) =
                    (RawKernel.regular 1 : RawKernel Coord)
                  simp [RawKernel.regular, RawKernel.mul]
                rw [hRegMul]
                exact mulKernelTermsRaw_regular_one (terms := opeRaw lhs.fields rhs.fields))
    _ = (ope lhs rhs).terms := by
          simpa [Expr.erase] using (ope_erase (lhs := lhs) (rhs := rhs)).symm

end ExprOrdered

end StringCodeLean.BCGhost

namespace StringCodeLean.OPECorrectness

open StringCodeLean.BCGhost
open StringCodeLean.Correctness

section Raw

variable {Coord : Type}

def contractCount (lhs : RawField Coord) (rhs : List (RawField Coord)) : Nat :=
  List.countP (fun field => (wickRaw lhs field).isSome) rhs

@[simp] theorem contractCount_nil (lhs : RawField Coord) :
    contractCount lhs [] = 0 := rfl

@[simp] theorem contractCount_cons (lhs head : RawField Coord) (tail : List (RawField Coord)) :
    contractCount lhs (head :: tail) =
      (if (wickRaw lhs head).isSome then 1 else 0) + contractCount lhs tail := by
  cases h : (wickRaw lhs head).isSome <;> simp [contractCount, h, Nat.add_comm]

@[simp] theorem contractTermsRawGo_length
    (lhs : RawField Coord) (baseKernel : RawKernel Coord)
    (prefixRev : List (RawField Coord)) (sign : Sign) :
    ∀ rhs, (contractTermsRawGo lhs baseKernel prefixRev sign rhs).length = contractCount lhs rhs
  | [] => by
      simp [contractTermsRawGo, contractCount]
  | head :: tail => by
      unfold contractTermsRawGo
      cases hWick : wickRaw lhs head <;>
        simp [hWick, contractTermsRawGo_length, contractCount]

@[simp] theorem contractTermsRaw_length
    (lhs : RawField Coord) (baseKernel : RawKernel Coord) (rhs : List (RawField Coord)) :
    (contractTermsRaw lhs baseKernel rhs).length = contractCount lhs rhs := by
  rw [contractTermsRaw]
  exact contractTermsRawGo_length lhs baseKernel [] .pos rhs

@[simp] theorem contractTermsRawGo_eq_nil_of_forall_wickRaw_eq_none
    (lhs : RawField Coord) (baseKernel : RawKernel Coord)
    (prefixRev : List (RawField Coord)) (sign : Sign) :
    ∀ rhs, (∀ field ∈ rhs, wickRaw lhs field = none) →
      contractTermsRawGo lhs baseKernel prefixRev sign rhs = []
  | [], _ => by
      simp [contractTermsRawGo]
  | head :: tail, hNone => by
      have hHead : wickRaw lhs head = none := hNone head (by simp)
      have hTail : ∀ field ∈ tail, wickRaw lhs field = none := by
        intro field hField
        exact hNone field (by simp [hField])
      simp [contractTermsRawGo, hHead, contractTermsRawGo_eq_nil_of_forall_wickRaw_eq_none lhs baseKernel (head :: prefixRev) sign.flip tail hTail]

@[simp] theorem contractTermsRaw_eq_nil_of_forall_wickRaw_eq_none
    (lhs : RawField Coord) (baseKernel : RawKernel Coord) (rhs : List (RawField Coord))
    (hNone : ∀ field ∈ rhs, wickRaw lhs field = none) :
    contractTermsRaw lhs baseKernel rhs = [] := by
  simpa [contractTermsRaw] using
    contractTermsRawGo_eq_nil_of_forall_wickRaw_eq_none lhs baseKernel [] .pos rhs hNone

@[simp] theorem wickRaw_eq_none_of_sameSpecies
    (lhs rhs : RawField Coord) (h : lhs.species = rhs.species) :
    wickRaw lhs rhs = none := by
  cases lhs with
  | mk lspecies lderiv lcoord =>
    cases rhs with
    | mk rspecies rderiv rcoord =>
      cases lspecies <;> cases rspecies <;> simp at h <;> simp [wickRaw]

end Raw

section Ordered

variable {Coord : Type} [Ord Coord]

@[simp] theorem regularInsertTermRaw_length
    (lhs : RawField Coord) (base : RawTerm Coord) :
    (regularInsertTermRaw lhs base).length =
      match insertRaw lhs base.remainder with
      | Signed.zero => 0
      | Signed.nonzero _ _ => 1 := by
  unfold regularInsertTermRaw
  cases insertRaw lhs base.remainder <;> simp

@[simp] theorem actFieldOnTermRaw_length
    (lhs : RawField Coord) (base : RawTerm Coord) :
    (actFieldOnTermRaw lhs base).length =
      (match insertRaw lhs base.remainder with
      | Signed.zero => 0
      | Signed.nonzero _ _ => 1) +
      contractCount lhs base.remainder := by
  unfold actFieldOnTermRaw
  rw [List.length_append, regularInsertTermRaw_length, contractTermsRaw_length]

def applyFieldsRaw : List (RawField Coord) → List (RawTerm Coord) → List (RawTerm Coord)
  | [], terms => terms
  | head :: tail, terms => applyFieldOnTermsRaw head (applyFieldsRaw tail terms)

@[simp] theorem applyFieldsRaw_nil (terms : List (RawTerm Coord)) :
    applyFieldsRaw [] terms = terms := rfl

@[simp] theorem applyFieldsRaw_cons
    (head : RawField Coord) (tail : List (RawField Coord)) (terms : List (RawTerm Coord)) :
    applyFieldsRaw (head :: tail) terms = applyFieldOnTermsRaw head (applyFieldsRaw tail terms) := rfl

@[simp] theorem applyFieldsRaw_append_terms
    (fields : List (RawField Coord)) (terms₁ terms₂ : List (RawTerm Coord)) :
    applyFieldsRaw fields (terms₁ ++ terms₂) =
      applyFieldsRaw fields terms₁ ++ applyFieldsRaw fields terms₂ := by
  induction fields with
  | nil =>
      simp [applyFieldsRaw]
  | cons field fields ih =>
      simp [applyFieldsRaw, ih]

@[simp] theorem applyFieldsRaw_append_fields
    (fields₁ fields₂ : List (RawField Coord)) (terms : List (RawTerm Coord)) :
    applyFieldsRaw (fields₁ ++ fields₂) terms =
      applyFieldsRaw fields₁ (applyFieldsRaw fields₂ terms) := by
  induction fields₁ with
  | nil =>
      simp [applyFieldsRaw]
  | cons field fields ih =>
      simp [applyFieldsRaw, ih]

@[simp] theorem opeRaw_eq_applyFieldsRaw (lhs rhs : List (RawField Coord)) :
    opeRaw lhs rhs = applyFieldsRaw lhs [{ kernel := RawKernel.regular 1, remainder := rhs }] := by
  induction lhs with
  | nil =>
      simp [opeRaw, applyFieldsRaw]
  | cons field fields ih =>
      simp [opeRaw, applyFieldsRaw, ih]

@[simp] theorem opeRaw_append_left
    (lhs₁ lhs₂ rhs : List (RawField Coord)) :
    opeRaw (lhs₁ ++ lhs₂) rhs = applyFieldsRaw lhs₁ (opeRaw lhs₂ rhs) := by
  rw [opeRaw_eq_applyFieldsRaw, applyFieldsRaw_append_fields, opeRaw_eq_applyFieldsRaw]

@[simp] theorem opeRaw_singleton
    (lhs : RawField Coord) (rhs : List (RawField Coord)) :
    opeRaw [lhs] rhs =
      regularInsertTermRaw lhs { kernel := RawKernel.regular 1, remainder := rhs } ++
      contractTermsRaw lhs (RawKernel.regular 1) rhs := by
  simp [opeRaw, actFieldOnTermRaw]

@[simp] theorem opeRaw_singleton_eq_regularInsert_of_forall_wickRaw_eq_none
    (lhs : RawField Coord) (rhs : List (RawField Coord))
    (hNone : ∀ field ∈ rhs, wickRaw lhs field = none) :
    opeRaw [lhs] rhs =
      regularInsertTermRaw lhs { kernel := RawKernel.regular 1, remainder := rhs } := by
  rw [opeRaw_singleton]
  rw [contractTermsRaw_eq_nil_of_forall_wickRaw_eq_none lhs (RawKernel.regular 1) rhs hNone]
  simp

@[simp] theorem opeField_erase_eq_regularInsert_of_forall_wickRaw_eq_none
    (lhs : Field Coord .holo g₁ w₁) (rhs : NOProd Coord .holo g₂ w₂)
    (hNone : ∀ field ∈ rhs.fields, wickRaw lhs.raw field = none) :
    (opeField lhs rhs).erase =
      regularInsertTermRaw lhs.raw { kernel := RawKernel.regular 1, remainder := rhs.fields } := by
  rw [opeField_erase]
  exact opeRaw_singleton_eq_regularInsert_of_forall_wickRaw_eq_none lhs.raw rhs.fields hNone

end Ordered

section ExprOrdered

variable {Coord : Type} [Ord Coord]

@[simp] theorem opeExpr_zero_left
    (rhs : Expr Coord .holo g₂ w₂) :
    opeExpr (0 : Expr Coord .holo g₁ w₁) rhs = 0 := by
  apply Expr.ext
  calc
    (opeExpr (0 : Expr Coord .holo g₁ w₁) rhs).terms
        = opeExprRaw (0 : Expr Coord .holo g₁ w₁).terms rhs.terms := by
            simpa using (opeExpr_erase (lhs := (0 : Expr Coord .holo g₁ w₁)) (rhs := rhs))
    _ = [] := by
          rw [show (0 : Expr Coord .holo g₁ w₁).terms = [] by rfl]
          simp [opeExprRaw]
    _ = (0 : Expr Coord .holo (g₁ + g₂) (w₁ + w₂)).terms := rfl

@[simp] theorem opeExpr_zero_right
    (lhs : Expr Coord .holo g₁ w₁) :
    opeExpr lhs (0 : Expr Coord .holo g₂ w₂) = 0 := by
  apply Expr.ext
  calc
    (opeExpr lhs (0 : Expr Coord .holo g₂ w₂)).terms
        = opeExprRaw lhs.terms (0 : Expr Coord .holo g₂ w₂).terms := by
            simpa using (opeExpr_erase (lhs := lhs) (rhs := (0 : Expr Coord .holo g₂ w₂)))
    _ = [] := by
          rw [show (0 : Expr Coord .holo g₂ w₂).terms = [] by rfl]
          induction lhs.terms with
          | nil =>
              simp [opeExprRaw]
          | cons term terms ih =>
              simp [opeExprRaw, applyTermOnTermsRaw, ih]
    _ = (0 : Expr Coord .holo (g₁ + g₂) (w₁ + w₂)).terms := rfl

@[simp] theorem opeExpr_add_left
    (lhs₁ lhs₂ : Expr Coord .holo g₁ w₁) (rhs : Expr Coord .holo g₂ w₂) :
    opeExpr (lhs₁ + lhs₂) rhs = opeExpr lhs₁ rhs + opeExpr lhs₂ rhs := by
  apply Expr.ext
  calc
    (opeExpr (lhs₁ + lhs₂) rhs).terms
        = opeExprRaw (lhs₁ + lhs₂).terms rhs.terms := by
            simpa using (opeExpr_erase (lhs := lhs₁ + lhs₂) (rhs := rhs))
    _ = opeExprRaw lhs₁.terms rhs.terms ++ opeExprRaw lhs₂.terms rhs.terms := by
          rw [show (lhs₁ + lhs₂).terms = lhs₁.terms ++ lhs₂.terms by rfl]
          exact opeExprRaw_append_left lhs₁.terms lhs₂.terms rhs.terms
    _ = (opeExpr lhs₁ rhs + opeExpr lhs₂ rhs).terms := by
          rw [show (opeExpr lhs₁ rhs + opeExpr lhs₂ rhs).terms =
              (opeExpr lhs₁ rhs).terms ++ (opeExpr lhs₂ rhs).terms by rfl]
          rw [show (opeExpr lhs₁ rhs).terms = opeExprRaw lhs₁.terms rhs.terms by
            simpa using (opeExpr_erase (lhs := lhs₁) (rhs := rhs))]
          rw [show (opeExpr lhs₂ rhs).terms = opeExprRaw lhs₂.terms rhs.terms by
            simpa using (opeExpr_erase (lhs := lhs₂) (rhs := rhs))]

theorem opeExpr_add_right_eqv
    (lhs : Expr Coord .holo g₁ w₁) (rhs₁ rhs₂ : Expr Coord .holo g₂ w₂) :
    (opeExpr lhs (rhs₁ + rhs₂)).Eqv (opeExpr lhs rhs₁ + opeExpr lhs rhs₂) := by
  rw [Expr.eqv_erase]
  simpa [opeExpr_erase, Expr.add_erase] using
    opeExprRaw_append_right_perm lhs.terms rhs₁.terms rhs₂.terms

set_option linter.unnecessarySimpa false in
theorem opeExpr_add_left_eqv
    (lhs₁ lhs₂ : Expr Coord .holo g₁ w₁) (rhs : Expr Coord .holo g₂ w₂) :
    (opeExpr (lhs₁ + lhs₂) rhs).Eqv (opeExpr lhs₁ rhs + opeExpr lhs₂ rhs) := by
  simpa [opeExpr_add_left] using
    (Expr.eqv_refl (opeExpr lhs₁ rhs + opeExpr lhs₂ rhs))

@[simp] theorem opeExpr_smul_left
    (scalar : Int) (lhs : Expr Coord .holo g₁ w₁) (rhs : Expr Coord .holo g₂ w₂) :
    opeExpr (scalar • lhs) rhs = scalar • opeExpr lhs rhs := by
  apply Expr.ext
  calc
    (opeExpr (scalar • lhs) rhs).terms
        = opeExprRaw (scalar • lhs).terms rhs.terms := by
            simpa using (opeExpr_erase (lhs := scalar • lhs) (rhs := rhs))
    _ = (opeExprRaw lhs.terms rhs.terms).map (RawTerm.scale scalar) := by
          rw [show (scalar • lhs).terms = lhs.terms.map (RawTerm.scale scalar) by rfl]
          exact opeExprRaw_scale_left scalar lhs.terms rhs.terms
    _ = (scalar • opeExpr lhs rhs).terms := by
          rw [show (scalar • opeExpr lhs rhs).terms =
              (opeExpr lhs rhs).terms.map (RawTerm.scale scalar) by rfl]
          rw [show (opeExpr lhs rhs).terms = opeExprRaw lhs.terms rhs.terms by
            simpa using (opeExpr_erase (lhs := lhs) (rhs := rhs))]

@[simp] theorem opeExpr_smul_right
    (scalar : Int) (lhs : Expr Coord .holo g₁ w₁) (rhs : Expr Coord .holo g₂ w₂) :
    opeExpr lhs (scalar • rhs) = scalar • opeExpr lhs rhs := by
  apply Expr.ext
  calc
    (opeExpr lhs (scalar • rhs)).terms
        = opeExprRaw lhs.terms (scalar • rhs).terms := by
            simpa using (opeExpr_erase (lhs := lhs) (rhs := scalar • rhs))
    _ = (opeExprRaw lhs.terms rhs.terms).map (RawTerm.scale scalar) := by
          rw [show (scalar • rhs).terms = rhs.terms.map (RawTerm.scale scalar) by rfl]
          exact opeExprRaw_scale_right scalar lhs.terms rhs.terms
    _ = (scalar • opeExpr lhs rhs).terms := by
          rw [show (scalar • opeExpr lhs rhs).terms =
              (opeExpr lhs rhs).terms.map (RawTerm.scale scalar) by rfl]
          rw [show (opeExpr lhs rhs).terms = opeExprRaw lhs.terms rhs.terms by
            simpa using (opeExpr_erase (lhs := lhs) (rhs := rhs))]

@[simp] theorem opeExpr_toExpr_eq_ope
    (lhs : NOProd Coord .holo g₁ w₁) (rhs : NOProd Coord .holo g₂ w₂) :
    opeExpr lhs.toExpr rhs.toExpr = ope lhs rhs :=
  opeExpr_toExpr lhs rhs

end ExprOrdered

end StringCodeLean.OPECorrectness
