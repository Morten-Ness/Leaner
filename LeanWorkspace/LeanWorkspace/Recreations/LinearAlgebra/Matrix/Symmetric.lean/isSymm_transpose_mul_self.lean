import Mathlib

variable {α β n m R : Type*}

theorem isSymm_transpose_mul_self [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α) :
    (Aᵀ * A).IsSymm := transpose_mul _ _

