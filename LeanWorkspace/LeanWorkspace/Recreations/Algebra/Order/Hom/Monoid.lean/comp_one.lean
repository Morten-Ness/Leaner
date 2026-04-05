import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α →*o β}

theorem comp_one (f : β →*o γ) : f.comp (1 : α →*o β) = 1 := OrderMonoidHom.ext fun _ => map_one f

