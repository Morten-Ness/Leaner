import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.submatrix {A : Matrix n n α} (h : A.IsSymm) (f : m → n) : (A.submatrix f f).IsSymm := (transpose_submatrix _ _ _).trans (h.symm ▸ rfl)

