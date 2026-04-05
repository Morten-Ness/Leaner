import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) = single a b₁ + single a b₂ := (zipWith_single_single _ _ _ _ _).symm

