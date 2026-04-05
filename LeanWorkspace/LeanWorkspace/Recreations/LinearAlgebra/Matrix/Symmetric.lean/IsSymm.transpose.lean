import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.transpose {A : Matrix n n α} (h : A.IsSymm) : Aᵀ.IsSymm := congr_arg _ h

