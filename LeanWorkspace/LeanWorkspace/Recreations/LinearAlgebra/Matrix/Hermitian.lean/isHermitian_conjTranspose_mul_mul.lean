import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [NonUnitalSemiring α] [StarRing α]

theorem isHermitian_conjTranspose_mul_mul [Fintype m] {A : Matrix m m α} (B : Matrix m n α)
    (hA : A.IsHermitian) : (Bᴴ * A * B).IsHermitian := by
  simp only [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

