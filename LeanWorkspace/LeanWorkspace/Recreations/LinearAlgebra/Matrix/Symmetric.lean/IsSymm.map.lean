import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.map {A : Matrix n n α} (h : A.IsSymm) (f : α → β) : (A.map f).IsSymm := by
  rw [Matrix.IsSymm, ← transpose_map, h.eq]

