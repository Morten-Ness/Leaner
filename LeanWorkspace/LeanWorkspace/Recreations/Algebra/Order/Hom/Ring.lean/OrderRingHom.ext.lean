import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α]

variable [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ] [Preorder γ] [NonAssocSemiring δ]
  [Preorder δ]

theorem ext {f g : α →+*o β} (h : ∀ a, f a = g a) : f = g := DFunLike.ext f g h

