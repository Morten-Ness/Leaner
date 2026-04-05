import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

theorem ext ⦃f g : α →ₙ+* β⦄ : (∀ x, f x = g x) → f = g := DFunLike.ext _ _

