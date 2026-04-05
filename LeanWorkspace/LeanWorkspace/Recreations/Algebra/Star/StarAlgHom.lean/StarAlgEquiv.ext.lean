import Mathlib

variable {F R A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A]
  [Star B] [Add C] [Mul C] [SMul R C] [Star C]

theorem ext {f g : A ≃⋆ₐ[R] B} (h : ∀ a, f a = g a) : f = g := DFunLike.ext f g h

