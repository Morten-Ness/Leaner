import Mathlib

variable {ι α R S : Type*}

variable {S : Type*} [Semiring S] [PartialOrder S]

variable {R : Type*} [Semiring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_add (x y) : abv (x + y) ≤ abv x + abv y := abv_add' x y

