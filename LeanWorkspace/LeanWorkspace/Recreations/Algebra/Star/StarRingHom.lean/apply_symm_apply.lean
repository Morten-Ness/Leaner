import Mathlib

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

theorem apply_symm_apply (e : A ≃⋆+* B) : ∀ x, e (e.symm x) = x := e.toRingEquiv.apply_symm_apply

