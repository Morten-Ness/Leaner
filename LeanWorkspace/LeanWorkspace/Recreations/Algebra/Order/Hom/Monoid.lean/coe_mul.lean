import Mathlib

variable {F α β γ δ : Type*}

variable [CommMonoid α] [Preorder α]
  [CommMonoid β] [Preorder β]
  [CommMonoid γ] [Preorder γ]

theorem coe_mul [IsOrderedMonoid β] (f g : α →*o β) : ⇑(f * g) = f * g := rfl

