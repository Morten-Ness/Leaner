import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoid M]

theorem rel_associated_iff_map_eq_map {p q : Multiset M} :
    Multiset.Rel Associated p q ↔ p.map Associates.mk = q.map Associates.mk := by
  rw [← Multiset.rel_eq, Multiset.rel_map]
  simp only [mk_eq_mk_iff_associated]

