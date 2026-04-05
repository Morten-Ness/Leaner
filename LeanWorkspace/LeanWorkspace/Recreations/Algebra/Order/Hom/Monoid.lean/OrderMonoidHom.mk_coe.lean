import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α →*o β}

theorem mk_coe (f : α →*o β) (h) : OrderMonoidHom.mk (f : α →* β) h = f := by
  ext
  rfl

