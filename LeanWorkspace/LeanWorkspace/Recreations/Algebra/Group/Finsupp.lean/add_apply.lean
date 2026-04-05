import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem add_apply (g₁ g₂ : ι →₀ M) (a : ι) : (g₁ + g₂) a = g₁ a + g₂ a := rfl

