import StringCodeLean.BCGhostTyped

namespace StringCodeLean.Correctness

open StringCodeLean.BCGhost

section Raw

variable {Coord : Type}

@[simp] def scaleTerm (scalar : Int) (term : RawTerm Coord) : RawTerm Coord :=
  { term with kernel := term.kernel.scale scalar }

@[simp] theorem scaleTerm_remainder (scalar : Int) (term : RawTerm Coord) :
    (scaleTerm scalar term).remainder = term.remainder := rfl

@[simp] theorem scaleTerm_ghost (scalar : Int) (term : RawTerm Coord) :
    (scaleTerm scalar term).ghost = term.ghost := rfl

@[simp] theorem scaleTerm_weight (scalar : Int) (term : RawTerm Coord) :
    (scaleTerm scalar term).weight = term.weight := by
  simp [scaleTerm, RawTerm.weight]

end Raw

section Ordered

variable {Coord : Type} [Ord Coord]

@[simp] theorem insertRaw_length (field : RawField Coord) (fields : List (RawField Coord)) :
    match insertRaw field fields with
    | Signed.zero => True
    | Signed.nonzero _ ordered => ordered.length = fields.length + 1 := by
  induction fields with
  | nil =>
      simp [insertRaw]
  | cons head tail ih =>
      unfold insertRaw
      cases hcmp : RawField.compare field head with
      | lt =>
          simp
      | eq =>
          simp
      | gt =>
          cases hrec : insertRaw field tail with
          | zero =>
              simp
          | nonzero sign rest =>
              have ih' : rest.length = tail.length + 1 := by
                simpa [hrec] using ih
              simpa [hrec] using ih'

@[simp] theorem normalOrderRaw_length (fields : List (RawField Coord)) :
    ∀ {sign ordered},
      normalOrderRaw fields = Signed.nonzero sign ordered →
      ordered.length = fields.length := by
  induction fields with
  | nil =>
      intro sign ordered h
      cases h
      simp
  | cons field tail ih =>
      intro sign ordered h
      unfold normalOrderRaw at h
      cases hTail : normalOrderRaw tail with
      | zero =>
          simp [hTail] at h
      | nonzero signTail orderedTail =>
          cases hIns : insertRaw field orderedTail with
          | zero =>
              simp [hTail, hIns] at h
          | nonzero signIns ordered' =>
              simp [hTail, hIns] at h
              rcases h with ⟨_, rfl⟩
              have hTailLen : orderedTail.length = tail.length := by
                exact ih hTail
              have hInsLen : ordered'.length = orderedTail.length + 1 := by
                simpa [hIns] using insertRaw_length field orderedTail
              simp [hInsLen, hTailLen]

@[simp] theorem normalOrderRaw_totalGhost (fields : List (RawField Coord)) :
    ∀ {sign ordered},
      normalOrderRaw fields = Signed.nonzero sign ordered →
      totalGhost ordered = totalGhost fields := by
  induction fields with
  | nil =>
      intro sign ordered h
      cases h
      simp [totalGhost]
  | cons field tail ih =>
      intro sign ordered h
      unfold normalOrderRaw at h
      cases hTail : normalOrderRaw tail with
      | zero =>
          simp [hTail] at h
      | nonzero signTail orderedTail =>
          cases hIns : insertRaw field orderedTail with
          | zero =>
              simp [hTail, hIns] at h
          | nonzero signIns ordered' =>
              simp [hTail, hIns] at h
              rcases h with ⟨_, rfl⟩
              have hTailGhost : totalGhost orderedTail = totalGhost tail := by
                exact ih hTail
              have hInsGhost : totalGhost ordered' = field.ghost + totalGhost orderedTail := by
                simpa [hIns] using insertRaw_totalGhost field orderedTail
              calc
                totalGhost ordered' = field.ghost + totalGhost orderedTail := hInsGhost
                _ = field.ghost + totalGhost tail := by rw [hTailGhost]
                _ = totalGhost (field :: tail) := by simp [totalGhost, totalBy]

@[simp] theorem normalOrderRaw_totalWeight (fields : List (RawField Coord)) :
    ∀ {sign ordered},
      normalOrderRaw fields = Signed.nonzero sign ordered →
      totalWeight ordered = totalWeight fields := by
  induction fields with
  | nil =>
      intro sign ordered h
      cases h
      simp [totalWeight]
  | cons field tail ih =>
      intro sign ordered h
      unfold normalOrderRaw at h
      cases hTail : normalOrderRaw tail with
      | zero =>
          simp [hTail] at h
      | nonzero signTail orderedTail =>
          cases hIns : insertRaw field orderedTail with
          | zero =>
              simp [hTail, hIns] at h
          | nonzero signIns ordered' =>
              simp [hTail, hIns] at h
              rcases h with ⟨_, rfl⟩
              have hTailWeight : totalWeight orderedTail = totalWeight tail := by
                exact ih hTail
              have hInsWeight : totalWeight ordered' = field.weight + totalWeight orderedTail := by
                simpa [hIns] using insertRaw_totalWeight field orderedTail
              calc
                totalWeight ordered' = field.weight + totalWeight orderedTail := hInsWeight
                _ = field.weight + totalWeight tail := by rw [hTailWeight]
                _ = totalWeight (field :: tail) := by simp [totalWeight, totalBy]

def grassmannParity (fields : List (RawField Coord)) : Bool :=
  fields.length % 2 = 1

@[simp] theorem normalOrderRaw_grassmannParity
    {fields : List (RawField Coord)} {sign : Sign} {ordered : List (RawField Coord)}
    (h : normalOrderRaw fields = Signed.nonzero sign ordered) :
    grassmannParity ordered = grassmannParity fields := by
  have hLen : ordered.length = fields.length := by
    exact normalOrderRaw_length fields h
  simp [grassmannParity, hLen]

@[simp] theorem normalOrderRaw_pair_lt
    (lhs rhs : RawField Coord) (h : RawField.compare lhs rhs = .lt) :
    normalOrderRaw [lhs, rhs] = Signed.nonzero .pos [lhs, rhs] := by
  simp [normalOrderRaw, insertRaw, h]
  native_decide

@[simp] theorem normalOrderRaw_pair_eq
    (lhs rhs : RawField Coord) (h : RawField.compare lhs rhs = .eq) :
    normalOrderRaw [lhs, rhs] = Signed.zero := by
  simp [normalOrderRaw, insertRaw, h]

@[simp] theorem normalOrderRaw_pair_gt
    (lhs rhs : RawField Coord) (h : RawField.compare lhs rhs = .gt) :
    normalOrderRaw [lhs, rhs] = Signed.nonzero .neg [rhs, lhs] := by
  simp [normalOrderRaw, insertRaw, h]
  native_decide

@[simp] theorem normalOrderTwo_lt
    (lhs : Field Coord .holo g₁ w₁) (rhs : Field Coord .holo g₂ w₂)
    (h : RawField.compare lhs.raw rhs.raw = .lt) :
    (normalOrderTwo lhs rhs).erase =
      [{ kernel := RawKernel.regular 1, remainder := [lhs.raw, rhs.raw] }] := by
  rw [normalOrderTwo_erase]
  simp [regularInsertTermRaw, insertRaw, h, RawKernel.scale, Sign.toInt]

@[simp] theorem normalOrderTwo_eq
    (lhs : Field Coord .holo g₁ w₁) (rhs : Field Coord .holo g₂ w₂)
    (h : RawField.compare lhs.raw rhs.raw = .eq) :
    (normalOrderTwo lhs rhs).erase = [] := by
  rw [normalOrderTwo_erase]
  simp [regularInsertTermRaw, insertRaw, h]

@[simp] theorem normalOrderTwo_gt
    (lhs : Field Coord .holo g₁ w₁) (rhs : Field Coord .holo g₂ w₂)
    (h : RawField.compare lhs.raw rhs.raw = .gt) :
    (normalOrderTwo lhs rhs).erase =
      [{ kernel := RawKernel.regular (-1), remainder := [rhs.raw, lhs.raw] }] := by
  rw [normalOrderTwo_erase]
  simp [regularInsertTermRaw, insertRaw, h, RawKernel.scale, Sign.toInt, Sign.flip]

@[simp] theorem applyFieldOnTermsRaw_nil (lhs : RawField Coord) :
    applyFieldOnTermsRaw lhs [] = [] := by
  rw [applyFieldOnTermsRaw_eq_flatMap]
  simp

@[simp] theorem applyFieldOnTermsRaw_append
    (lhs : RawField Coord) (bases₁ bases₂ : List (RawTerm Coord)) :
    applyFieldOnTermsRaw lhs (bases₁ ++ bases₂) =
      applyFieldOnTermsRaw lhs bases₁ ++ applyFieldOnTermsRaw lhs bases₂ := by
  rw [applyFieldOnTermsRaw_eq_flatMap, applyFieldOnTermsRaw_eq_flatMap, applyFieldOnTermsRaw_eq_flatMap]
  exact List.flatMap_append (xs := bases₁) (ys := bases₂) (f := actFieldOnTermRaw lhs)

end Ordered

end StringCodeLean.Correctness
