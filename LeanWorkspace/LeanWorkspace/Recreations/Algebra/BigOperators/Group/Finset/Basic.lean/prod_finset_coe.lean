import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_finset_coe (f : ι → M) (s : Finset ι) : (∏ i : (s : Set ι), f i) = ∏ i ∈ s, f i := Finset.prod_coe_sort s f

