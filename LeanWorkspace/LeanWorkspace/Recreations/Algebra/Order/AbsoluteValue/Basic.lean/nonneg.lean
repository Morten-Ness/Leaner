import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

theorem nonneg (x : R) : 0 ≤ abv x := abv.nonneg' x

