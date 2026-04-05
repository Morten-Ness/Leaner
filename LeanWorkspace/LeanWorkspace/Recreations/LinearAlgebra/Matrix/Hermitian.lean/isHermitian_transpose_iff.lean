import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Star α] [Star β]

theorem isHermitian_transpose_iff {A : Matrix n n α} : Aᵀ.IsHermitian ↔ A.IsHermitian := ⟨by intro h; rw [← transpose_transpose A]; exact Matrix.IsHermitian.transpose h, Matrix.IsHermitian.transpose⟩

