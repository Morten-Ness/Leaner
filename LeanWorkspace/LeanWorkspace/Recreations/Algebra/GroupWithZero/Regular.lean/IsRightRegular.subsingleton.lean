import Mathlib

variable [MulZeroClass R] {a b : R}

theorem IsRightRegular.subsingleton (h : IsRightRegular (0 : R)) : Subsingleton R := ⟨fun a b => h <| Eq.trans (mul_zero a) (mul_zero b).symm⟩

