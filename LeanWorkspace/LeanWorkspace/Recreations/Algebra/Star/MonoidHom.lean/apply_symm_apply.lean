import Mathlib

variable {F A B C D : Type*}

variable [Mul A] [Mul B] [Mul C] [Mul D]

variable [Star A] [Star B] [Star C] [Star D]

theorem apply_symm_apply (e : A ≃⋆* B) : ∀ x, e (e.symm x) = x := e.toMulEquiv.apply_symm_apply

