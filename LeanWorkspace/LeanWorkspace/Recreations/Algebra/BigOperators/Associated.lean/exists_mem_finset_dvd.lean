import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] {p : M₀}

theorem exists_mem_finset_dvd (hp : Prime p) {s : Finset ι} {f : ι → M₀} :
    p ∣ s.prod f → ∃ i ∈ s, p ∣ f i := Prime.exists_mem_multiset_map_dvd hp

