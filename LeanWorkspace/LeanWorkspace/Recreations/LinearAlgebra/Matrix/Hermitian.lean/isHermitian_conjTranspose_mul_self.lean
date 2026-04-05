import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [NonUnitalSemiring α] [StarRing α]

theorem isHermitian_conjTranspose_mul_self [Fintype m] (A : Matrix m n α) :
    (Aᴴ * A).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]

