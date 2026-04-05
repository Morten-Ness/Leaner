import Mathlib

variable {R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

theorem mul_le_right {x y : Set.Icc (0 : R) 1} : x * y ≤ y := (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq (one_mul _)

