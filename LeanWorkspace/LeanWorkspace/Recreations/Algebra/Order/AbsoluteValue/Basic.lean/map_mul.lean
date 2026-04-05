import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

theorem map_mul (x y : R) : abv (x * y) = abv x * abv y := abv.map_mul' x y

