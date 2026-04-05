import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Star α] [Star β]

theorem IsHermitian.reindex {A : Matrix n n α} (h : A.IsHermitian) (f : n ≃ m) :
    (A.reindex f f).IsHermitian := by
  rw [reindex_apply]
  apply submatrix h

