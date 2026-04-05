import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_mul_pow_card {b : M} : (∏ a ∈ s, f a) * b ^ #s = ∏ a ∈ s, f a * b := (Finset.prod_const b).symm ▸ Finset.prod_mul_distrib.symm

