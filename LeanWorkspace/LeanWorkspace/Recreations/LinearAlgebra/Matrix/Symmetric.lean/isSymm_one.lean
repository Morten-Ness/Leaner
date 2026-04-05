import Mathlib

variable {α β n m R : Type*}

theorem isSymm_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α).IsSymm := transpose_one

