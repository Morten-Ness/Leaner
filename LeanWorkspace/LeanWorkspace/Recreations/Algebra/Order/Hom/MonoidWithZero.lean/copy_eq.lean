import Mathlib

variable {F α β γ δ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] [MulZeroOneClass α] [MulZeroOneClass β]
  [MulZeroOneClass γ] [MulZeroOneClass δ] {f g : α →*₀o β}

theorem copy_eq (f : α →*₀o β) (f' : α → β) (h : f' = f) : f.copy f' h = f := DFunLike.ext' h

