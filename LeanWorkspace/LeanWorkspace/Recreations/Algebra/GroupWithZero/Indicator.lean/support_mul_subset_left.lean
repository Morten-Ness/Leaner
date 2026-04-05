import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroClass M₀]

theorem support_mul_subset_left (f g : ι → M₀) : support (fun x ↦ f x * g x) ⊆ support f := fun x hfg hf ↦ hfg <| by simp only [hf, zero_mul]

