import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroClass M₀]

theorem support_mul_subset_right (f g : ι → M₀) : support (fun x ↦ f x * g x) ⊆ support g := fun x hfg hg => hfg <| by simp only [hg, mul_zero]

