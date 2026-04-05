import Mathlib

variable [MulZeroClass R] {a b : R}

theorem isRightRegular_zero_iff_subsingleton : IsRightRegular (0 : R) ↔ Subsingleton R := ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

