import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Ring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

theorem map_sub_eq_zero_iff (a b : R) : abv (a - b) = 0 ↔ a = b := AbsoluteValue.eq_zero abv.trans sub_eq_zero

