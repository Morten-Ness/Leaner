import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.reindex {A : Matrix n n α} (h : A.IsSymm) (f : n ≃ m) : (A.reindex f f).IsSymm := by
  rw [reindex_apply]
  apply submatrix h

