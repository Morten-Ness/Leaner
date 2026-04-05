import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_dvd_prod_of_subset {ι M : Type*} [CommMonoid M] (s t : Finset ι) (f : ι → M)
    (h : s ⊆ t) : (∏ i ∈ s, f i) ∣ ∏ i ∈ t, f i := Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| by simpa

