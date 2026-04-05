import Mathlib

variable {F A B C D : Type*}

variable [Mul A] [Mul B] [Mul C] [Mul D]

variable [Star A] [Star B] [Star C] [Star D]

theorem symm_apply_apply (e : A ≃⋆* B) : ∀ x, e.symm (e x) = x := e.toMulEquiv.symm_apply_apply

