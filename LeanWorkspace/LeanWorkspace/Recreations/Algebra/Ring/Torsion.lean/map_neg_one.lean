import Mathlib

variable {R M : Type*} [Ring R] [Monoid M] [IsMulTorsionFree M] (f : R →* M)

theorem map_neg_one : f (-1) = 1 := (pow_eq_one_iff_left (Nat.succ_ne_zero 1)).1 <| by rw [← map_pow, neg_one_sq, map_one]

