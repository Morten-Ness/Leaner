import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.neg [Neg α] {A : Matrix n n α} (h : A.IsSymm) : (-A).IsSymm := (transpose_neg _).trans (congr_arg _ h)

