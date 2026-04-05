import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_single_of_mem {s : Finset ι} {f : ι → M} (a : ι) (h : a ∈ s)
    (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) : ∏ x ∈ s, f x = f a := by
  calc
    ∏ x ∈ s, f x = ∏ x ∈ {a}, f x := by
      { refine (Finset.prod_subset ?_ ?_).symm
        · intro _ H
          rwa [mem_singleton.1 H]
        · simpa only [mem_singleton] }
    _ = f a := Finset.prod_singleton _ _

