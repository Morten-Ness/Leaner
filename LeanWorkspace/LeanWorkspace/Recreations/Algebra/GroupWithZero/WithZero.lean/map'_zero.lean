import Mathlib

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulOneClass β] [MulOneClass γ]

theorem map'_zero (f : α →* β) : WithZero.map' f 0 = 0 := rfl

