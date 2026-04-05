import Mathlib

variable {F α β γ δ : Type*}

variable [LinearOrderedCommMonoidWithZero α] [LinearOrderedCommMonoidWithZero β]
  [LinearOrderedCommMonoidWithZero γ]

theorem mul_comp (g₁ g₂ : β →*₀o γ) (f : α →*₀o β) : (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

