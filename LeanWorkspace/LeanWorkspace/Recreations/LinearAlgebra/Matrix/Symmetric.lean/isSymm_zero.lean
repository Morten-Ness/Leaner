import Mathlib

variable {α β n m R : Type*}

theorem isSymm_zero [Zero α] : (0 : Matrix n n α).IsSymm := transpose_zero

