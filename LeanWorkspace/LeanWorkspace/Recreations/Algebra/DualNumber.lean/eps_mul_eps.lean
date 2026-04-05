import Mathlib

variable {R A B : Type*}

theorem eps_mul_eps [Semiring R] : (ε * ε : R[ε]) = 0 := inr_mul_inr _ _ _

