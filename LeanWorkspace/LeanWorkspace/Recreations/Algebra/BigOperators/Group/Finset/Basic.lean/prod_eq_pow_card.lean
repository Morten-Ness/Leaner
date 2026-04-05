import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_pow_card {b : M} (hf : ∀ a ∈ s, f a = b) : ∏ a ∈ s, f a = b ^ #s := (Finset.prod_congr rfl hf).trans <| Finset.prod_const _

