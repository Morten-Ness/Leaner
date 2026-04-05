import Mathlib

variable {α β n m R : Type*}

theorem isSymm_mul_transpose_self [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α) :
    (A * Aᵀ).IsSymm := transpose_mul _ _

