import Mathlib

variable {α β n m R : Type*}

theorem isSymm_add_transpose_self [AddCommSemigroup α] (A : Matrix n n α) : (A + Aᵀ).IsSymm := add_comm _ _

