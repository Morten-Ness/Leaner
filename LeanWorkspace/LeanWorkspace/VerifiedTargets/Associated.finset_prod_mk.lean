import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoid M]

theorem finset_prod_mk {p : Finset ι} {f : ι → M} :
    (∏ i ∈ p, Associates.mk (f i)) = Associates.mk (∏ i ∈ p, f i) := by
  rw [Finset.prod_eq_multiset_prod, ← Function.comp_def, ← Multiset.map_map, Associates.prod_mk,
    ← Finset.prod_eq_multiset_prod]

