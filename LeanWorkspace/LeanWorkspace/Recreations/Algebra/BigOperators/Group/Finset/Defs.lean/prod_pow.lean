import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_pow (s : Finset ι) (n : ℕ) (f : ι → M) : ∏ x ∈ s, f x ^ n = (∏ x ∈ s, f x) ^ n := Multiset.prod_map_pow

