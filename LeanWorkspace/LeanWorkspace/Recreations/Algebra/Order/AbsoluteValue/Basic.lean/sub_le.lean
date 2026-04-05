import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Ring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

theorem sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) := by
  simpa [sub_eq_add_neg, add_assoc] using AbsoluteValue.add_le abv (a - b) (b - c)

