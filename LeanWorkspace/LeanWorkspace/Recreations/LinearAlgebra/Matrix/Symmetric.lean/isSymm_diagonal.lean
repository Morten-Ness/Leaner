import Mathlib

variable {α β n m R : Type*}

theorem isSymm_diagonal [DecidableEq n] [Zero α] (v : n → α) : (diagonal v).IsSymm := diagonal_transpose _

