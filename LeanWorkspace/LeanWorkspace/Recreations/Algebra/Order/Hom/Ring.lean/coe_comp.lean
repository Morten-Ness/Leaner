import Mathlib

variable {F α β γ δ : Type*}

variable [NonAssocSemiring α] [Preorder α]

variable [NonAssocSemiring β] [Preorder β] [NonAssocSemiring γ] [Preorder γ] [NonAssocSemiring δ]
  [Preorder δ]

theorem coe_comp (f : β →+*o γ) (g : α →+*o β) : ⇑(f.comp g) = f ∘ g := rfl

