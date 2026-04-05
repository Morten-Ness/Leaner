import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α]

variable [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ] [Preorder γ] [NonAssocSemiring δ]
  [Preorder δ]

theorem comp_assoc (f : γ →+*o δ) (g : β →+*o γ) (h : α →+*o β) :
    (f.comp g).comp h = f.comp (g.comp h) := rfl

