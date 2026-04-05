import Mathlib

variable {ι α R S : Type*}

variable {S : Type*} [Semiring S] [PartialOrder S]

variable {R : Type*} [Semiring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_pos {a : R} : 0 < abv a ↔ a ≠ 0 := AbsoluteValue.pos_iff (IsAbsoluteValue.toAbsoluteValue abv)

