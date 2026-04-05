import Mathlib

variable {F α β γ δ : Type*}

variable [LinearOrderedCommMonoidWithZero α] [LinearOrderedCommMonoidWithZero β]
  [LinearOrderedCommMonoidWithZero γ]

theorem comp_mul (g : β →*₀o γ) (f₁ f₂ : α →*₀o β) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := OrderMonoidWithZeroHom.ext fun _ => map_mul g _ _

