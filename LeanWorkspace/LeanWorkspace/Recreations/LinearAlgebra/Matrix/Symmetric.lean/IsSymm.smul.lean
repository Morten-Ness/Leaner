import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.smul [SMul R α] {A : Matrix n n α} (h : A.IsSymm) (k : R) : (k • A).IsSymm := (transpose_smul _ _).trans (congr_arg _ h)

