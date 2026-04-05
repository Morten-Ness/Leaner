import Mathlib

variable {ι F M N O G H : Type*}

theorem sub_apply [SubNegZeroMonoid G] (g₁ g₂ : ι →₀ G) (a : ι) : (g₁ - g₂) a = g₁ a - g₂ a := rfl

