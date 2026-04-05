import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_coe_sort : ∏ i : s, f i = ∏ i ∈ s, f i := Finset.prod_attach _ _

