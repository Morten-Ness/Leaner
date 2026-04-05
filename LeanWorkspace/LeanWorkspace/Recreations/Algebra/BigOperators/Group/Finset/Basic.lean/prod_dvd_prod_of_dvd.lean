import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_dvd_prod_of_dvd (f g : ι → M) (h : ∀ i ∈ s, f i ∣ g i) :
    ∏ i ∈ s, f i ∣ ∏ i ∈ s, g i := Multiset.prod_dvd_prod_of_dvd _ _ h

