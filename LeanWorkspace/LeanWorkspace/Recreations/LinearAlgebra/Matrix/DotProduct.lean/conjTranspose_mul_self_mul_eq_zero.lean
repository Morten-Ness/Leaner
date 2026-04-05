import Mathlib

variable {m n p R : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [PartialOrder R] [NonUnitalRing R] [StarRing R] [StarOrderedRing R]

variable [NoZeroDivisors R]

theorem conjTranspose_mul_self_mul_eq_zero {p} (A : Matrix m n R) (B : Matrix n p R) :
    (Aᴴ * A) * B = 0 ↔ A * B = 0 := by
  refine ⟨fun h => ?_, fun h => by simp only [Matrix.mul_assoc, h, Matrix.mul_zero]⟩
  apply_fun (Bᴴ * ·) at h
  rwa [Matrix.mul_zero, Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul,
    Matrix.conjTranspose_mul_self_eq_zero] at h

