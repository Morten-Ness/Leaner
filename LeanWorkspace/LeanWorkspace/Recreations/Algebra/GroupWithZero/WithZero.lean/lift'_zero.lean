import Mathlib

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulZeroOneClass β]

theorem lift'_zero (f : α →* β) : lift' f (0 : WithZero α) = 0 := rfl

