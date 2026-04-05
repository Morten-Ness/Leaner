import Mathlib

variable {F α β γ δ : Type*}

variable [LinearOrderedCommMonoidWithZero α] [LinearOrderedCommMonoidWithZero β]
  [LinearOrderedCommMonoidWithZero γ]

theorem coe_mul (f g : α →*₀o β) : ⇑(f * g) = f * g := rfl

