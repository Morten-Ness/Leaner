import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem single_add_apply (a : ι) (m₁ m₂ : M) (b : ι) :
    single a (m₁ + m₂) b = single a m₁ b + single a m₂ b := by simp

