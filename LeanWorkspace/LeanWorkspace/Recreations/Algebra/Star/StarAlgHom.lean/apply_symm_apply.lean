import Mathlib

variable {F R A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A]
  [Star B] [Add C] [Mul C] [SMul R C] [Star C]

theorem apply_symm_apply (e : A ≃⋆ₐ[R] B) : ∀ x, e (e.symm x) = x := e.toStarRingEquiv.apply_symm_apply

