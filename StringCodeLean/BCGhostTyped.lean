import StringCodeLean.BCGhost

namespace StringCodeLean.BCGhost

@[simp] theorem wickRaw_weight_of_some
    {lhs rhs : RawField Coord} {kernel : RawKernel Coord}
    (h : wickRaw lhs rhs = some kernel) :
    kernel.weight = lhs.weight + rhs.weight := by
  cases lhs with
  | mk ls ld lz =>
    cases rhs with
    | mk rs rd rz =>
      cases ls <;> cases rs
      · simp [wickRaw] at h
      · simp [wickRaw] at h
        cases h
        simp [RawField.weight, RawKernel.weight, totalPoleOrder]
        omega
      · simp [wickRaw] at h
        cases h
        simp [RawField.weight, RawKernel.weight, totalPoleOrder]
        omega
      · simp [wickRaw] at h

@[simp] theorem wickRaw_ghost_cancel
    {lhs rhs : RawField Coord} {kernel : RawKernel Coord}
    (h : wickRaw lhs rhs = some kernel) :
    lhs.ghost + rhs.ghost = 0 := by
  cases lhs with
  | mk ls ld lz =>
    cases rhs with
    | mk rs rd rz =>
      cases ls <;> cases rs
      · simp [wickRaw] at h
      · simp [wickRaw, RawField.ghost] at h ⊢
      · simp [wickRaw, RawField.ghost] at h ⊢
      · simp [wickRaw] at h


def wick (lhs : Field Coord .holo g₁ w₁) (rhs : Field Coord .holo g₂ w₂) :
    Option (Kernel Coord (w₁ + w₂)) :=
  match h : wickRaw lhs.raw rhs.raw with
  | none => none
  | some kernel =>
      some {
        raw := kernel
        hw := by
          have hWeight := wickRaw_weight_of_some h
          rw [lhs.hw, rhs.hw] at hWeight
          simpa using hWeight
      }

@[simp] theorem wick_erase
    (lhs : Field Coord .holo g₁ w₁) (rhs : Field Coord .holo g₂ w₂) :
    Option.map Kernel.erase (wick lhs rhs) = wickRaw lhs.raw rhs.raw := by
  unfold wick
  split <;> simp [*]

variable [Ord Coord]

@[simp] theorem insertRaw_totalBy
    (grade : RawField Coord → Int) (field : RawField Coord) (fields : List (RawField Coord)) :
    match insertRaw field fields with
    | Signed.zero => True
    | Signed.nonzero _ ordered => totalBy grade ordered = grade field + totalBy grade fields := by
  induction fields with
  | nil =>
      simp [insertRaw, totalBy]
  | cons head tail ih =>
      unfold insertRaw
      cases hcmp : RawField.compare field head with
      | lt =>
          simp [totalBy]
      | eq =>
          simp
      | gt =>
          cases hrec : insertRaw field tail with
          | zero =>
              simp
          | nonzero sign rest =>
              have ih' : totalBy grade rest = grade field + totalBy grade tail := by
                simpa [hrec] using ih
              simp [totalBy, ih']
              omega

set_option linter.unnecessarySimpa false in
@[simp] theorem insertRaw_totalGhost (field : RawField Coord) (fields : List (RawField Coord)) :
    match insertRaw field fields with
    | Signed.zero => True
    | Signed.nonzero _ ordered => totalGhost ordered = field.ghost + totalGhost fields := by
  simpa [totalGhost] using insertRaw_totalBy RawField.ghost field fields

set_option linter.unnecessarySimpa false in
@[simp] theorem insertRaw_totalWeight (field : RawField Coord) (fields : List (RawField Coord)) :
    match insertRaw field fields with
    | Signed.zero => True
    | Signed.nonzero _ ordered => totalWeight ordered = field.weight + totalWeight fields := by
  simpa [totalWeight] using insertRaw_totalBy RawField.weight field fields
@[simp] theorem regularInsertTermRaw_term_grade
    (kernelGrade : RawKernel Coord → Int) (fieldGrade : RawField Coord → Int)
    (hScale : ∀ scalar kernel, kernelGrade (kernel.scale scalar) = kernelGrade kernel)
    {lhs : RawField Coord} {base term : RawTerm Coord}
    (h : term ∈ regularInsertTermRaw lhs base) :
    term.grade kernelGrade fieldGrade = fieldGrade lhs + base.grade kernelGrade fieldGrade := by
  unfold regularInsertTermRaw at h
  cases hins : insertRaw lhs base.remainder with
  | zero =>
      simp [hins] at h
  | nonzero sign ordered =>
      simp [hins] at h
      rcases h with rfl
      have hOrdered : totalBy fieldGrade ordered = fieldGrade lhs + totalBy fieldGrade base.remainder := by
        simpa [hins] using insertRaw_totalBy fieldGrade lhs base.remainder
      have hKernel : kernelGrade (base.kernel.scale sign.toInt) = kernelGrade base.kernel := hScale sign.toInt base.kernel
      simp [RawTerm.grade, hOrdered, hKernel]
      omega

@[simp] theorem regularInsertTermRaw_term_ghost
    {lhs : RawField Coord} {base term : RawTerm Coord}
    (h : term ∈ regularInsertTermRaw lhs base) :
    term.ghost = lhs.ghost + base.ghost := by
  simpa using
    (regularInsertTermRaw_term_grade
      (kernelGrade := fun _ => 0)
      (fieldGrade := RawField.ghost)
      (hScale := fun _ _ => rfl)
      h)

@[simp] theorem regularInsertTermRaw_term_weight
    {lhs : RawField Coord} {base term : RawTerm Coord}
    (h : term ∈ regularInsertTermRaw lhs base) :
    term.weight = lhs.weight + base.weight := by
  simpa using
    (regularInsertTermRaw_term_grade
      (kernelGrade := RawKernel.weight)
      (fieldGrade := RawField.weight)
      (hScale := RawKernel.scale_weight)
      h)

omit [Ord Coord] in
@[simp] theorem contractTermsRawGo_term_grade
    (kernelGrade : RawKernel Coord → Int) (fieldGrade : RawField Coord → Int)
    (hScale : ∀ scalar kernel, kernelGrade (kernel.scale scalar) = kernelGrade kernel)
    (hMul : ∀ lhs rhs, kernelGrade (lhs * rhs) = kernelGrade lhs + kernelGrade rhs)
    (hWick : ∀ {lhs rhs kernel}, wickRaw lhs rhs = some kernel → kernelGrade kernel = fieldGrade lhs + fieldGrade rhs)
    (lhs : RawField Coord) (baseKernel : RawKernel Coord)
    (prefixRev : List (RawField Coord)) (sign : Sign) :
    ∀ {rhs : List (RawField Coord)} {term : RawTerm Coord},
      term ∈ contractTermsRawGo lhs baseKernel prefixRev sign rhs →
      term.grade kernelGrade fieldGrade =
        fieldGrade lhs + kernelGrade baseKernel + totalBy fieldGrade prefixRev + totalBy fieldGrade rhs
  | [], term, h => by cases h
  | head :: tail, term, h => by
      unfold contractTermsRawGo at h
      cases hWickRaw : wickRaw lhs head with
      | none =>
          simp [hWickRaw] at h
          have ih :=
            contractTermsRawGo_term_grade kernelGrade fieldGrade hScale hMul hWick lhs baseKernel
              (head :: prefixRev) sign.flip h
          simp [totalBy, Int.add_assoc, Int.add_left_comm, Int.add_comm] at ih ⊢
          omega
      | some kernel =>
          simp [hWickRaw] at h
          rcases h with h | h
          ·
            rcases h with rfl
            have hk := hWick hWickRaw
            have hbase := hMul baseKernel kernel
            have hscaled := hScale sign.toInt (baseKernel * kernel)
            simp [RawTerm.grade, totalBy_append, totalBy_reverse, totalBy, hk, hbase, hscaled,
              Int.add_assoc, Int.add_left_comm, Int.add_comm]
          ·
            have ih :=
              contractTermsRawGo_term_grade kernelGrade fieldGrade hScale hMul hWick lhs baseKernel
                (head :: prefixRev) sign.flip h
            simp [totalBy, Int.add_assoc, Int.add_left_comm, Int.add_comm] at ih ⊢
            omega

omit [Ord Coord] in
@[simp] theorem contractTermsRaw_term_grade
    (kernelGrade : RawKernel Coord → Int) (fieldGrade : RawField Coord → Int)
    (hScale : ∀ scalar kernel, kernelGrade (kernel.scale scalar) = kernelGrade kernel)
    (hMul : ∀ lhs rhs, kernelGrade (lhs * rhs) = kernelGrade lhs + kernelGrade rhs)
    (hWick : ∀ {lhs rhs kernel}, wickRaw lhs rhs = some kernel → kernelGrade kernel = fieldGrade lhs + fieldGrade rhs)
    (lhs : RawField Coord) (baseKernel : RawKernel Coord) :
    ∀ {rhs : List (RawField Coord)} {term : RawTerm Coord},
      term ∈ contractTermsRaw lhs baseKernel rhs →
      term.grade kernelGrade fieldGrade =
        fieldGrade lhs + kernelGrade baseKernel + totalBy fieldGrade rhs
  | rhs, term, h => by
      simpa [contractTermsRaw, totalBy] using
        (contractTermsRawGo_term_grade kernelGrade fieldGrade hScale hMul hWick lhs baseKernel [] .pos
          (rhs := rhs) (term := term) h)

omit [Ord Coord] in
@[simp] theorem contractTermsRaw_term_ghost (lhs : RawField Coord) (baseKernel : RawKernel Coord) :
    ∀ {rhs : List (RawField Coord)} {term : RawTerm Coord},
      term ∈ contractTermsRaw lhs baseKernel rhs →
      term.ghost = lhs.ghost + totalGhost rhs
  | rhs, term, h => by
      simpa using
        (contractTermsRaw_term_grade
          (kernelGrade := fun _ => 0)
          (fieldGrade := RawField.ghost)
          (hScale := fun _ _ => rfl)
          (hMul := fun _ _ => rfl)
          (hWick := fun hWick => by
            have hGhost := wickRaw_ghost_cancel hWick
            simpa using hGhost.symm)
          lhs baseKernel h)

omit [Ord Coord] in
@[simp] theorem contractTermsRaw_term_weight (lhs : RawField Coord) (baseKernel : RawKernel Coord) :
    ∀ {rhs : List (RawField Coord)} {term : RawTerm Coord},
      term ∈ contractTermsRaw lhs baseKernel rhs →
      term.weight = lhs.weight + baseKernel.weight + totalWeight rhs
  | rhs, term, h => by
      simpa using
        (contractTermsRaw_term_grade
          (kernelGrade := RawKernel.weight)
          (fieldGrade := RawField.weight)
          (hScale := RawKernel.scale_weight)
          (hMul := RawKernel.mul_weight)
          (hWick := fun hWick => wickRaw_weight_of_some hWick)
          lhs baseKernel h)
@[simp] theorem actFieldOnTermRaw_term_grade
    (kernelGrade : RawKernel Coord → Int) (fieldGrade : RawField Coord → Int)
    (hScale : ∀ scalar kernel, kernelGrade (kernel.scale scalar) = kernelGrade kernel)
    (hMul : ∀ lhs rhs, kernelGrade (lhs * rhs) = kernelGrade lhs + kernelGrade rhs)
    (hWick : ∀ {lhs rhs kernel}, wickRaw lhs rhs = some kernel → kernelGrade kernel = fieldGrade lhs + fieldGrade rhs)
    {lhs : RawField Coord} {base term : RawTerm Coord}
    (h : term ∈ actFieldOnTermRaw lhs base) :
    term.grade kernelGrade fieldGrade = fieldGrade lhs + base.grade kernelGrade fieldGrade := by
  unfold actFieldOnTermRaw at h
  simp at h
  rcases h with h | h
  · exact regularInsertTermRaw_term_grade kernelGrade fieldGrade hScale h
  ·
    have hGrade := contractTermsRaw_term_grade kernelGrade fieldGrade hScale hMul hWick lhs base.kernel h
    simpa [RawTerm.grade, Int.add_assoc, Int.add_left_comm, Int.add_comm] using hGrade

@[simp] theorem actFieldOnTermRaw_term_ghost
    {lhs : RawField Coord} {base term : RawTerm Coord}
    (h : term ∈ actFieldOnTermRaw lhs base) :
    term.ghost = lhs.ghost + base.ghost := by
  simpa using
    (actFieldOnTermRaw_term_grade
      (kernelGrade := fun _ => 0)
      (fieldGrade := RawField.ghost)
      (hScale := fun _ _ => rfl)
          (hMul := fun _ _ => rfl)
          (hWick := fun hWick => by
        have hGhost := wickRaw_ghost_cancel hWick
        simpa using hGhost.symm)
      h)

@[simp] theorem actFieldOnTermRaw_term_weight
    {lhs : RawField Coord} {base term : RawTerm Coord}
    (h : term ∈ actFieldOnTermRaw lhs base) :
    term.weight = lhs.weight + base.weight := by
  simpa using
    (actFieldOnTermRaw_term_grade
      (kernelGrade := RawKernel.weight)
      (fieldGrade := RawField.weight)
      (hScale := RawKernel.scale_weight)
      (hMul := RawKernel.mul_weight)
      (hWick := fun hWick => wickRaw_weight_of_some hWick)
      h)
@[simp] theorem applyFieldOnTermsRaw_eq_flatMap
    (lhs : RawField Coord) (bases : List (RawTerm Coord)) :
    applyFieldOnTermsRaw lhs bases = List.flatMap (actFieldOnTermRaw lhs) bases := by
  induction bases with
  | nil => rfl
  | cons base bases ih =>
      simp [applyFieldOnTermsRaw, List.flatMap, ih]
omit [Ord Coord] in
@[simp] theorem contractTermsRawArrayAcc_toList
    (lhs : RawField Coord) (baseKernel : RawKernel Coord)
    (prefixRev : List (RawField Coord)) (sign : Sign) :
    ∀ (rhs : List (RawField Coord)) (acc : Array (RawTerm Coord)),
      (contractTermsRawArrayAcc lhs baseKernel prefixRev sign rhs acc).toList =
        acc.toList ++ contractTermsRawGo lhs baseKernel prefixRev sign rhs
  | [], acc => by
      simp [contractTermsRawArrayAcc, contractTermsRawGo]
  | head :: tail, acc => by
      unfold contractTermsRawArrayAcc contractTermsRawGo
      cases hWick : wickRaw lhs head <;>
        simp [contractTermsRawArrayAcc_toList, Array.toList_push, List.append_assoc]

omit [Ord Coord] in
set_option linter.unnecessarySimpa false in
@[simp] theorem contractTermsRawFast_eq
    (lhs : RawField Coord) (baseKernel : RawKernel Coord) (rhs : List (RawField Coord)) :
    contractTermsRawFast lhs baseKernel rhs = contractTermsRaw lhs baseKernel rhs := by
  have h := contractTermsRawArrayAcc_toList lhs baseKernel [] .pos rhs (#[] : Array (RawTerm Coord))
  simpa [contractTermsRawFast, contractTermsRaw] using h
@[simp] theorem actFieldOnTermRawArrayAcc_toList
    (lhs : RawField Coord) (base : RawTerm Coord) :
    ∀ (acc : Array (RawTerm Coord)),
      (actFieldOnTermRawArrayAcc lhs base acc).toList =
        acc.toList ++ actFieldOnTermRaw lhs base
  | acc => by
      unfold actFieldOnTermRawArrayAcc actFieldOnTermRaw regularInsertTermRaw
      cases hins : insertRaw lhs base.remainder with
      | zero =>
          simp [contractTermsRawArrayAcc_toList, contractTermsRaw]
      | nonzero sign ordered =>
          simp [contractTermsRawArrayAcc_toList, contractTermsRaw, Array.toList_push, List.append_assoc]

@[simp] theorem applyFieldOnTermsRawArrayAcc_toList
    (lhs : RawField Coord) :
    ∀ (bases : List (RawTerm Coord)) (acc : Array (RawTerm Coord)),
      (applyFieldOnTermsRawArrayAcc lhs bases acc).toList =
        acc.toList ++ applyFieldOnTermsRaw lhs bases
  | [], acc => by
      simp [applyFieldOnTermsRawArrayAcc]
  | base :: bases, acc => by
      rw [applyFieldOnTermsRawArrayAcc]
      rw [applyFieldOnTermsRawArrayAcc_toList]
      rw [actFieldOnTermRawArrayAcc_toList]
      simp [applyFieldOnTermsRaw, List.append_assoc]
set_option linter.unnecessarySimpa false in
@[simp] theorem applyFieldOnTermsRawFast_eq
    (lhs : RawField Coord) (bases : List (RawTerm Coord)) :
    applyFieldOnTermsRawFast lhs bases = applyFieldOnTermsRaw lhs bases := by
  rw [applyFieldOnTermsRawFast]
  have h := applyFieldOnTermsRawArrayAcc_toList lhs bases (#[] : Array (RawTerm Coord))
  simpa using h
@[simp] theorem opeRawFast_eq :
    ∀ (lhs rhs : List (RawField Coord)), opeRawFast lhs rhs = opeRaw lhs rhs
  | [], rhs => by
      simp [opeRawFast, opeRaw]
  | head :: tail, rhs => by
      simp [opeRawFast, opeRaw, opeRawFast_eq, applyFieldOnTermsRawFast_eq]

@[simp] theorem opeRaw_term_grade
    (kernelGrade : RawKernel Coord → Int) (fieldGrade : RawField Coord → Int)
    (hRegular : ∀ coeff, kernelGrade (RawKernel.regular (Coord := Coord) coeff) = 0)
    (hScale : ∀ scalar kernel, kernelGrade (kernel.scale scalar) = kernelGrade kernel)
    (hMul : ∀ lhs rhs, kernelGrade (lhs * rhs) = kernelGrade lhs + kernelGrade rhs)
    (hWick : ∀ {lhs rhs kernel}, wickRaw lhs rhs = some kernel → kernelGrade kernel = fieldGrade lhs + fieldGrade rhs) :
    ∀ {lhs rhs : List (RawField Coord)} {term : RawTerm Coord},
      term ∈ opeRaw lhs rhs →
      term.grade kernelGrade fieldGrade = totalBy fieldGrade lhs + totalBy fieldGrade rhs
  | [], rhs, term, h => by
      simp [opeRaw] at h
      rcases h with rfl
      simpa [RawTerm.grade, totalBy, RawKernel.regular] using
        congrArg (fun x => x + totalBy fieldGrade rhs) (hRegular 1)
  | head :: tail, rhs, term, h => by
      simp [opeRaw] at h
      rcases h with ⟨base, hBase, hAct⟩
      have hBaseGrade := opeRaw_term_grade kernelGrade fieldGrade hRegular hScale hMul hWick hBase
      have hActGrade := actFieldOnTermRaw_term_grade kernelGrade fieldGrade hScale hMul hWick hAct
      simp [RawTerm.grade, totalBy, Int.add_assoc, Int.add_left_comm] at hBaseGrade hActGrade ⊢
      omega

@[simp] theorem opeRaw_term_ghost :
    ∀ {lhs rhs : List (RawField Coord)} {term : RawTerm Coord},
      term ∈ opeRaw lhs rhs →
      term.ghost = totalGhost lhs + totalGhost rhs
  | lhs, rhs, term, h => by
      simpa using
        (opeRaw_term_grade
          (kernelGrade := fun _ => 0)
          (fieldGrade := RawField.ghost)
          (hRegular := fun _ => rfl)
          (hScale := fun _ _ => rfl)
          (hMul := fun _ _ => rfl)
          (hWick := fun hWick => by
            have hGhost := wickRaw_ghost_cancel hWick
            simpa using hGhost.symm)
          h)

@[simp] theorem opeRaw_term_weight :
    ∀ {lhs rhs : List (RawField Coord)} {term : RawTerm Coord},
      term ∈ opeRaw lhs rhs →
      term.weight = totalWeight lhs + totalWeight rhs
  | lhs, rhs, term, h => by
      simpa using
        (opeRaw_term_grade
          (kernelGrade := RawKernel.weight)
          (fieldGrade := RawField.weight)
          (hRegular := RawKernel.weight_regular)
          (hScale := RawKernel.scale_weight)
          (hMul := RawKernel.mul_weight)
          (hWick := fun hWick => wickRaw_weight_of_some hWick)
          h)


private def mkHoloExpr
    (terms : List (RawTerm Coord))
    (hGhost : ∀ term ∈ terms, term.ghost = g)
    (hWeight : ∀ term ∈ terms, term.weight = w) :
    Expr Coord .holo g w :=
  { terms := terms
    hχ := by
      intro term hTerm field hField
      simp [RawField.chirality]
    hg := hGhost
    hw := hWeight }

omit [Ord Coord] in
@[simp] theorem mkHoloExpr_erase
    (terms : List (RawTerm Coord))
    (hGhost : ∀ term ∈ terms, term.ghost = g)
    (hWeight : ∀ term ∈ terms, term.weight = w) :
    (mkHoloExpr terms hGhost hWeight).erase = terms := rfl
def normalOrderTwo
    (lhs : Field Coord .holo g₁ w₁) (rhs : Field Coord .holo g₂ w₂) :
    Expr Coord .holo (g₁ + g₂) (w₁ + w₂) :=
  let base : RawTerm Coord := { kernel := RawKernel.regular 1, remainder := [rhs.raw] }
  let terms := regularInsertTermRaw lhs.raw base
  mkHoloExpr terms
    (hGhost := by
      intro term hTerm
      have hGhost := regularInsertTermRaw_term_ghost (lhs := lhs.raw) (base := base) (term := term) hTerm
      rw [lhs.hg] at hGhost
      simpa [base, totalGhost, totalBy, rhs.hg] using hGhost)
    (hWeight := by
      intro term hTerm
      have hWeight := regularInsertTermRaw_term_weight (lhs := lhs.raw) (base := base) (term := term) hTerm
      rw [lhs.hw] at hWeight
      simpa [base, totalWeight, totalBy, rhs.hw, Int.add_assoc, RawKernel.weight, totalPoleOrder] using hWeight)

@[simp] theorem normalOrderTwo_erase
    (lhs : Field Coord .holo g₁ w₁) (rhs : Field Coord .holo g₂ w₂) :
    (normalOrderTwo lhs rhs).erase = regularInsertTermRaw lhs.raw { kernel := RawKernel.regular 1, remainder := [rhs.raw] } := rfl


def ope
    (lhs : NOProd Coord .holo g₁ w₁) (rhs : NOProd Coord .holo g₂ w₂) :
    Expr Coord .holo (g₁ + g₂) (w₁ + w₂) :=
  let terms := opeRawFast lhs.fields rhs.fields
  mkHoloExpr terms
    (hGhost := by
      intro term hTerm
      change term ∈ opeRawFast lhs.fields rhs.fields at hTerm
      rw [opeRawFast_eq lhs.fields rhs.fields] at hTerm
      have hGhost := opeRaw_term_ghost (lhs := lhs.fields) (rhs := rhs.fields) (term := term) hTerm
      rw [lhs.hg, rhs.hg] at hGhost
      simpa using hGhost)
    (hWeight := by
      intro term hTerm
      change term ∈ opeRawFast lhs.fields rhs.fields at hTerm
      rw [opeRawFast_eq lhs.fields rhs.fields] at hTerm
      have hWeight := opeRaw_term_weight (lhs := lhs.fields) (rhs := rhs.fields) (term := term) hTerm
      rw [lhs.hw, rhs.hw] at hWeight
      simpa using hWeight)

@[simp] theorem ope_erase
    (lhs : NOProd Coord .holo g₁ w₁) (rhs : NOProd Coord .holo g₂ w₂) :
    (ope lhs rhs).erase = opeRaw lhs.fields rhs.fields := by
  simp [Expr.erase, ope, opeRawFast_eq, mkHoloExpr]


def opeField
    (lhs : Field Coord .holo g₁ w₁) (rhs : NOProd Coord .holo g₂ w₂) :
    Expr Coord .holo (g₁ + g₂) (w₁ + w₂) :=
  ope (NOProd.singleton lhs) rhs

@[simp] theorem opeField_erase
    (lhs : Field Coord .holo g₁ w₁) (rhs : NOProd Coord .holo g₂ w₂) :
    (opeField lhs rhs).erase = opeRaw [lhs.raw] rhs.fields := by
  simpa [opeField] using (ope_erase (lhs := NOProd.singleton lhs) (rhs := rhs))
@[simp] def WickSpec := @wickRaw

def OpeSpec [Ord Coord] (lhs rhs : List (RawField Coord)) : List (RawTerm Coord) :=
  opeRaw lhs rhs

end StringCodeLean.BCGhost
