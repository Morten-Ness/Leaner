import Mathlib

variable {F α β γ δ : Type*}

variable [LinearOrderedCommMonoidWithZero α] [LinearOrderedCommMonoidWithZero β]
  [LinearOrderedCommMonoidWithZero γ]

theorem mul_apply (f g : α →*₀o β) (a : α) : (f * g) a = f a * g a := rfl

