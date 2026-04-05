import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_ite [DecidableEq ι] {s : Finset ι} {f : ι → M} (a : ι)
    (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) :
    ∏ x ∈ s, f x = if a ∈ s then f a else 1 := by
  by_cases h : a ∈ s
  · simp [Finset.prod_eq_single_of_mem a h h₀, h]
  · replace h₀ : ∀ b ∈ s, f b = 1 := by grind
    simp +contextual [h₀]

