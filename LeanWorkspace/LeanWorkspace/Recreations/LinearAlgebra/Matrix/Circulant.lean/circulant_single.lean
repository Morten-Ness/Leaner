import Mathlib

variable {α β n R : Type*}

theorem circulant_single (n) [Semiring α] [DecidableEq n] [AddGroup n] [Fintype n] (a : α) :
    Matrix.circulant (Pi.single 0 a : n → α) = Matrix.scalar n a := by
  ext i j
  simp [Pi.single_apply, diagonal_apply, sub_eq_zero]

