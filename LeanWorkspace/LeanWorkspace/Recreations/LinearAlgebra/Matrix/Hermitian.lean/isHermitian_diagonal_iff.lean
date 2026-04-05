import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [AddMonoid α] [StarAddMonoid α]

theorem isHermitian_diagonal_iff [DecidableEq n] {d : n → α} :
    Matrix.IsHermitian (diagonal d) ↔ (∀ i : n, IsSelfAdjoint (d i)) := by
  simp [isSelfAdjoint_iff, Matrix.IsHermitian, conjTranspose, diagonal_transpose, diagonal_map]

