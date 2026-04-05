import Mathlib

variable {ι α R S : Type*}

variable {S : Type*} [Semiring S] [PartialOrder S]

variable {R : Type*} [Semiring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_zero : abv 0 = 0 := AbsoluteValue.map_zero (IsAbsoluteValue.toAbsoluteValue abv)

