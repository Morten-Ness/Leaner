import Mathlib

variable [MulZeroClass R] {a b : R}

theorem IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) : a ≠ 0 := la.left.ne_zero

