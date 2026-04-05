import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulOneClass α] [MulOneClass β]
  [MulOneClass γ] [MulOneClass δ] {f g : α →*o β}

theorem copy_eq (f : α →*o β) (f' : α → β) (h : f' = f) : f.copy f' h = f := DFunLike.ext' h

