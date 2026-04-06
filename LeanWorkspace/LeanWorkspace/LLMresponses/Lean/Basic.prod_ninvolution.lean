FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_ninvolution (g : ι → ι) (hg₁ : ∀ a, f a * f (g a) = 1) (hg₂ : ∀ a, f a ≠ 1 → g a ≠ a)
    (g_mem : ∀ a, g a ∈ s) (hg₃ : ∀ a, g (g a) = a) : ∏ x ∈ s, f x = 1 := by
  classical
  have hfa1 : ∀ a, f a = 1 := by
    intro a
    by_cases h : f a = 1
    · exact h
    · exfalso
      exact (hg₂ a h) (hg₃ a)
  simp [hfa1]
