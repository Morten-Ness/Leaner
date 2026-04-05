import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.conjTranspose [Star α] {A : Matrix n n α} (h : A.IsSymm) : Aᴴ.IsSymm := h.transpose.map _

