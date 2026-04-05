import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_filter_ne_one (s : Finset ι) [∀ x, Decidable (f x ≠ 1)] :
    ∏ x ∈ s with f x ≠ 1, f x = ∏ x ∈ s, f x := Finset.prod_filter_of_ne fun _ _ => id

