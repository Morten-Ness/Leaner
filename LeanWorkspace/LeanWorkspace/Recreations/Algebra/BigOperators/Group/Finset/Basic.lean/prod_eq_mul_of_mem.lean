import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_mul_of_mem {s : Finset ι} {f : ι → M} (a b : ι) (ha : a ∈ s) (hb : b ∈ s)
    (hn : a ≠ b) (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) : ∏ x ∈ s, f x = f a * f b := by
  haveI := Classical.decEq ι; let s' := ({a, b} : Finset ι)
  have hu : s' ⊆ s := by grind
  have hf : ∀ c ∈ s, c ∉ s' → f c = 1 := by grind
  rw [← Finset.prod_subset hu hf]
  exact Finset.prod_pair hn

