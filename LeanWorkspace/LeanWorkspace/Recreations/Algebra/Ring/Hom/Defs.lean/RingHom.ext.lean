import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

theorem ext ⦃f g : α →+* β⦄ : (∀ x, f x = g x) → f = g := DFunLike.ext _ _

