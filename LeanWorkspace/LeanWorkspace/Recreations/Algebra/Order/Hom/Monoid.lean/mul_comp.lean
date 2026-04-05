import Mathlib

variable {F α β γ δ : Type*}

variable [CommMonoid α] [Preorder α]
  [CommMonoid β] [Preorder β]
  [CommMonoid γ] [Preorder γ]

theorem mul_comp [IsOrderedMonoid γ] (g₁ g₂ : β →*o γ) (f : α →*o β) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

