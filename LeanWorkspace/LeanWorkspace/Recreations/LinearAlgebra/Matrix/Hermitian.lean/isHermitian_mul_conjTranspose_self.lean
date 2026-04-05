import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [NonUnitalSemiring α] [StarRing α]

theorem isHermitian_mul_conjTranspose_self [Fintype n] (A : Matrix m n α) :
    (A * Aᴴ).IsHermitian := by rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]

