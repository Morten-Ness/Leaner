import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [NonUnitalSemiring α] [StarRing α]

theorem isHermitian_mul_mul_conjTranspose [Fintype m] {A : Matrix m m α} (B : Matrix n m α)
    (hA : A.IsHermitian) : (B * A * Bᴴ).IsHermitian := by
  simp only [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

