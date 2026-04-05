import Mathlib

variable {F A B C D : Type*}

variable [Mul A] [Mul B] [Mul C] [Mul D]

variable [Star A] [Star B] [Star C] [Star D]

theorem ext {f g : A ≃⋆* B} (h : ∀ a, f a = g a) : f = g := DFunLike.ext f g h

