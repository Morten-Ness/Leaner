import Mathlib

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

theorem ext {f g : A ≃⋆+* B} (h : ∀ a, f a = g a) : f = g := DFunLike.ext f g h

