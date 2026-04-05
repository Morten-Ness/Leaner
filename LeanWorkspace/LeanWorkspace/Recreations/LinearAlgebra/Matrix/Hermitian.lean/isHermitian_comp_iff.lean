import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Star α] [Star β]

theorem isHermitian_comp_iff {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsHermitian ↔ A.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.IsHermitian, Matrix.conjTranspose_comp', comp .. |>.injective.eq_iff]

