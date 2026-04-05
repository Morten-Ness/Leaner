import Mathlib

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

theorem symm_apply_apply (e : A ≃⋆+* B) : ∀ x, e.symm (e x) = x := e.toRingEquiv.symm_apply_apply

