import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_transpose (A : Matrix n n R) : Matrix.trace Aᵀ = Matrix.trace A := rfl

