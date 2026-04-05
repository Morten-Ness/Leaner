import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

omit [IsDomain R] in
theorem Splits.of_splits_map_of_injective {S : Type*} [CommRing S] [IsDomain S] {i : R →+* S}
    (hi : Function.Injective i) (hf : Polynomial.Splits (f.map i))
    (hi : ∀ a ∈ (f.map i).roots, a ∈ i.range) : Polynomial.Splits f := by
  choose j hj using hi
  rw [Polynomial.splits_iff_exists_multiset]
  refine ⟨(f.map i).roots.pmap j fun _ ↦ id, map_injective i hi ?_⟩
  conv_lhs => rw [hf.eq_prod_roots, leadingCoeff_map_of_injective hi]
  simp [Multiset.pmap_eq_map, hj, Multiset.map_pmap, Polynomial.map_multiset_prod]

