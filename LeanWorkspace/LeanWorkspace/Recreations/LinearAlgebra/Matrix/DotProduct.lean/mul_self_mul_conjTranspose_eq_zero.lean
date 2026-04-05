import Mathlib

variable {m n p R : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [PartialOrder R] [NonUnitalRing R] [StarRing R] [StarOrderedRing R]

variable [NoZeroDivisors R]

theorem mul_self_mul_conjTranspose_eq_zero {p} (A : Matrix m n R) (B : Matrix p m R) :
    B * (A * Aᴴ) = 0 ↔ B * A = 0 := by
  rw [← conjTranspose_eq_zero, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.self_mul_conjTranspose_mul_eq_zero, ← conjTranspose_mul, conjTranspose_eq_zero]

