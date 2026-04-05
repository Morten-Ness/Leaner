import Mathlib

variable {ι α R S : Type*}

variable {S : Type*} [Ring S] [PartialOrder S]

variable {R : Type*} [Semiring R] (abv : R → S) [IsAbsoluteValue abv]

variable [IsDomain S]

theorem abv_pow [Nontrivial R] (abv : R → S) [IsAbsoluteValue abv] (a : R) (n : ℕ) :
    abv (a ^ n) = abv a ^ n := AbsoluteValue.map_pow (IsAbsoluteValue.toAbsoluteValue abv) a n

