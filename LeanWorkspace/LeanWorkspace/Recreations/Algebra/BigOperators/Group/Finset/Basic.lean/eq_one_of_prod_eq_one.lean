import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem eq_one_of_prod_eq_one {s : Finset ι} {f : ι → M} {a : ι} (hp : ∏ x ∈ s, f x = 1)
    (h1 : ∀ x ∈ s, x ≠ a → f x = 1) : ∀ x ∈ s, f x = 1 := by
  intro x hx
  classical
    by_cases h : x = a
    · rw [h]
      rw [h] at hx
      rw [← Finset.prod_subset (singleton_subset_iff.2 hx) fun t ht ha => h1 t ht (notMem_singleton.1 ha),
        Finset.prod_singleton] at hp
      exact hp
    · exact h1 x hx h

