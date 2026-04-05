import Mathlib

variable {m n p R : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [PartialOrder R] [NonUnitalRing R] [StarRing R] [StarOrderedRing R]

variable [NoZeroDivisors R]

theorem vecMul_self_mul_conjTranspose_eq_zero (A : Matrix m n R) (v : m → R) :
    v ᵥ* (A * Aᴴ) = 0 ↔ v ᵥ* A = 0 := by
  simpa only [conjTranspose_conjTranspose] using Matrix.vecMul_conjTranspose_mul_self_eq_zero Aᴴ _

