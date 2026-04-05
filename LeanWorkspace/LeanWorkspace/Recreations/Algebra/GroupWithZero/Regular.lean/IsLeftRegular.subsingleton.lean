import Mathlib

variable [MulZeroClass R] {a b : R}

theorem IsLeftRegular.subsingleton (h : IsLeftRegular (0 : R)) : Subsingleton R := ⟨fun a b => h <| Eq.trans (zero_mul a) (zero_mul b).symm⟩

