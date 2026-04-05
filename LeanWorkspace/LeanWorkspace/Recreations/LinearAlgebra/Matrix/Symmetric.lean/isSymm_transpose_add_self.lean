import Mathlib

variable {α β n m R : Type*}

theorem isSymm_transpose_add_self [AddCommSemigroup α] (A : Matrix n n α) : (Aᵀ + A).IsSymm := add_comm _ _

