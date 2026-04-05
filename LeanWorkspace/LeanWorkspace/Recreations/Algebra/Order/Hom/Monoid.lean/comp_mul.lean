import Mathlib

variable {F α β γ δ : Type*}

variable [CommMonoid α] [Preorder α]
  [CommMonoid β] [Preorder β]
  [CommMonoid γ] [Preorder γ]

theorem comp_mul [IsOrderedMonoid β] [IsOrderedMonoid γ] (g : β →*o γ) (f₁ f₂ : α →*o β) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := OrderMonoidHom.ext fun _ => map_mul g _ _

