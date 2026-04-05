import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_fold (s : Finset ι) (f : ι → M) : ∏ i ∈ s, f i = s.fold (β := M) (· * ·) 1 f := rfl

