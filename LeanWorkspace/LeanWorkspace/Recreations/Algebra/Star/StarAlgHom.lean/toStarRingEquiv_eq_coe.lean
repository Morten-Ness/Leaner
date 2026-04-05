import Mathlib

variable {F R A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A]
  [Star B] [Add C] [Mul C] [SMul R C] [Star C]

theorem toStarRingEquiv_eq_coe (e : A ≃⋆ₐ[R] B) : e.toStarRingEquiv = e := rfl

