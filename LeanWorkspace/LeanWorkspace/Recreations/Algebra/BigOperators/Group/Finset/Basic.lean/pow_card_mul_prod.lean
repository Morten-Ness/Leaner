import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem pow_card_mul_prod {b : M} : b ^ #s * ∏ a ∈ s, f a = ∏ a ∈ s, b * f a := (Finset.prod_const b).symm ▸ Finset.prod_mul_distrib.symm

