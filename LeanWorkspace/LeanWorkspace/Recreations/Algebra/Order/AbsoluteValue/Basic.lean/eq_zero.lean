import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

theorem eq_zero {x : R} : abv x = 0 ↔ x = 0 := abv.eq_zero' x

