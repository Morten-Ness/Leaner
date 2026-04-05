import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

theorem map_one_of_isLeftRegular (h : IsLeftRegular (abv 1)) : abv 1 = 1 := h <| by simp [← AbsoluteValue.map_mul abv]

