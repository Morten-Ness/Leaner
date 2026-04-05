import Mathlib

variable {ι α R S : Type*}

variable {S : Type*} [Semiring S] [PartialOrder S]

variable {R : Type*} [Semiring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_eq_zero {x} : abv x = 0 ↔ x = 0 := abv_eq_zero'

