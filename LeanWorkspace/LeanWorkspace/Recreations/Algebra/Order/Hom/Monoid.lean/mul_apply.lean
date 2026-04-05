import Mathlib

variable {F α β γ δ : Type*}

variable [CommMonoid α] [Preorder α]
  [CommMonoid β] [Preorder β]
  [CommMonoid γ] [Preorder γ]

theorem mul_apply [IsOrderedMonoid β] (f g : α →*o β) (a : α) : (f * g) a = f a * g a := rfl

