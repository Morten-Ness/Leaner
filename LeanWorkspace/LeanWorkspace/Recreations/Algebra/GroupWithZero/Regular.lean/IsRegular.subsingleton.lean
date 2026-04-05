import Mathlib

variable [MulZeroClass R] {a b : R}

theorem IsRegular.subsingleton (h : IsRegular (0 : R)) : Subsingleton R := h.left.subsingleton

