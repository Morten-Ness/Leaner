import Mathlib

variable [MulZeroClass R] {a b : R}

theorem isRegular_iff_subsingleton : IsRegular (0 : R) ↔ Subsingleton R := ⟨fun h => h.left.subsingleton, fun h =>
    ⟨isLeftRegular_zero_iff_subsingleton.mpr h, isRightRegular_zero_iff_subsingleton.mpr h⟩⟩

