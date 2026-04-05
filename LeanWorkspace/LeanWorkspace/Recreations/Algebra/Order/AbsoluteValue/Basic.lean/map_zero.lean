import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

theorem map_zero : abv 0 = 0 := AbsoluteValue.eq_zero abv.2 rfl

