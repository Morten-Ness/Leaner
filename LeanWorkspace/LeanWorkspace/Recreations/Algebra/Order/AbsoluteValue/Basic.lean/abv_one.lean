import Mathlib

variable {ι α R S : Type*}

variable {S : Type*} [Ring S] [PartialOrder S]

variable {R : Type*} [Semiring R] (abv : R → S) [IsAbsoluteValue abv]

variable [IsDomain S]

theorem abv_one [Nontrivial R] : abv 1 = 1 := AbsoluteValue.map_one (IsAbsoluteValue.toAbsoluteValue abv)

