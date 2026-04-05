import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α]

variable [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ] [Preorder γ] [NonAssocSemiring δ]
  [Preorder δ]

theorem comp_apply (f : β →+*o γ) (g : α →+*o β) (a : α) : f.comp g a = f (g a) := rfl

