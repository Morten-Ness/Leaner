import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.eq {A : Matrix n n α} (h : A.IsSymm) : Aᵀ = A := h

