import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] {p : M₀}

theorem exists_mem_multiset_map_dvd (hp : Prime p) {s : Multiset ι} {f : ι → M₀} :
    p ∣ (s.map f).prod → ∃ a ∈ s, p ∣ f a := fun h => by
  simpa only [exists_prop, Multiset.mem_map, exists_exists_and_eq_and] using
    Prime.exists_mem_multiset_dvd hp h

