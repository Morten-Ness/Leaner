import Mathlib

variable {α β n R : Type*}

theorem circulant_single_one (α n) [Zero α] [One α] [DecidableEq n] [AddGroup n] :
    Matrix.circulant (Pi.single 0 1 : n → α) = (1 : Matrix n n α) := by
  ext i j
  simp [one_apply, Pi.single_apply, sub_eq_zero]

