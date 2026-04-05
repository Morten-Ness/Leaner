import Mathlib

variable {ι α R S : Type*}

variable {S : Type*} [Ring S] [PartialOrder S]

variable {R : Type*} [Ring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) := by
  simpa [sub_eq_add_neg, add_assoc] using IsAbsoluteValue.abv_add abv (a - b) (b - c)

