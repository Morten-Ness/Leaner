import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem mul_le_left {x y : Set.Icc (0 : R) 1} : x * y ≤ x := (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq (mul_one _)

