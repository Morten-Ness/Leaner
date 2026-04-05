import Mathlib

variable {R M : Type*} [Ring R] [Monoid M] [IsMulTorsionFree M] (f : R →* M)

theorem map_sub_swap (x y : R) : f (x - y) = f (y - x) := by rw [← map_neg, neg_sub]

