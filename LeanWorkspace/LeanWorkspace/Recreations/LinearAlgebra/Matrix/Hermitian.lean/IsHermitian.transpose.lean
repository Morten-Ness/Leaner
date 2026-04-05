import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Star α] [Star β]

theorem IsHermitian.transpose {A : Matrix n n α} (h : A.IsHermitian) : Aᵀ.IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose, transpose_map]
  exact congr_arg Matrix.transpose h

