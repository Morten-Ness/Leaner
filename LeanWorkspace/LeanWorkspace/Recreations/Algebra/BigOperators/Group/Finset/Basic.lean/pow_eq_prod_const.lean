import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem pow_eq_prod_const (b : M) : ∀ n, b ^ n = ∏ _k ∈ range n, b := by simp

