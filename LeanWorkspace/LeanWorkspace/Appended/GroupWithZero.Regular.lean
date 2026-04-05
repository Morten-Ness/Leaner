import Mathlib

section

variable [MulZeroClass R] {a b : R}

theorem IsLeftRegular.ne_zero [Nontrivial R] (la : IsLeftRegular a) : a ≠ 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (la ?_)
  simp

end

section

variable [MulZeroClass R] {a b : R}

theorem IsLeftRegular.subsingleton (h : IsLeftRegular (0 : R)) : Subsingleton R := ⟨fun a b => h <| Eq.trans (zero_mul a) (zero_mul b).symm⟩

end

section

variable [MulZeroClass R] [IsCancelMulZero R] {a : R}

theorem IsRegular.of_ne_zero (a0 : a ≠ 0) : IsRegular a := ⟨fun _ _ => mul_left_cancel₀ a0, fun _ _ => mul_right_cancel₀ a0⟩

end

section

variable [MulZeroClass R] {a b : R}

theorem IsRightRegular.ne_zero [Nontrivial R] (ra : IsRightRegular a) : a ≠ 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (ra ?_)
  simp

end

section

variable [MulZeroClass R] {a b : R}

theorem IsRightRegular.subsingleton (h : IsRightRegular (0 : R)) : Subsingleton R := ⟨fun a b => h <| Eq.trans (mul_zero a) (mul_zero b).symm⟩

end

section

variable [MulZeroClass R] {a b : R}

theorem isLeftRegular_zero_iff_subsingleton : IsLeftRegular (0 : R) ↔ Subsingleton R := ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

end

section

variable [MulZeroClass R] {a b : R}

theorem isRegular_iff_subsingleton : IsRegular (0 : R) ↔ Subsingleton R := ⟨fun h => h.left.subsingleton, fun h =>
    ⟨isLeftRegular_zero_iff_subsingleton.mpr h, isRightRegular_zero_iff_subsingleton.mpr h⟩⟩

end

section

variable [MulZeroClass R] {a b : R}

theorem isRightRegular_zero_iff_subsingleton : IsRightRegular (0 : R) ↔ Subsingleton R := ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

end

section

variable [MulZeroClass R] {a b : R}

theorem not_isLeftRegular_zero_iff : ¬IsLeftRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, isLeftRegular_zero_iff_subsingleton, subsingleton_iff]
  push Not
  exact Iff.rfl

end

section

variable [MulZeroClass R] {a b : R}

theorem not_isRightRegular_zero_iff : ¬IsRightRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, isRightRegular_zero_iff_subsingleton, subsingleton_iff]
  push Not
  exact Iff.rfl

end
