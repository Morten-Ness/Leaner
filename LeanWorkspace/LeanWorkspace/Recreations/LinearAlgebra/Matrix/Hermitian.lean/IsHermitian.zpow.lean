import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [CommRing α] [StarRing α]

theorem IsHermitian.zpow [Fintype m] [DecidableEq m] {A : Matrix m m α} (h : A.IsHermitian)
    (k : ℤ) :
    (A ^ k).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_zpow, h]

