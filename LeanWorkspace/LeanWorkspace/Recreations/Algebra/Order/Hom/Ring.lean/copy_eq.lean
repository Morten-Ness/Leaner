import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α]

variable [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ] [Preorder γ] [NonAssocSemiring δ]
  [Preorder δ]

theorem copy_eq (f : α →+*o β) (f' : α → β) (h : f' = f) : f.copy f' h = f := DFunLike.ext' h

