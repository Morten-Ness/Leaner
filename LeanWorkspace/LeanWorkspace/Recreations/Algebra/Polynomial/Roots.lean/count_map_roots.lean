import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable {A B : Type*} [CommRing A] [CommRing B]

theorem count_map_roots [IsDomain A] [DecidableEq B] {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0)
    (b : B) :
    (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) := by
  rw [le_rootMultiplicity_iff hmap, ← Multiset.prod_replicate, ←
    Multiset.map_replicate fun a => X - C a]
  rw [← Multiset.filter_eq]
  refine
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| Multiset.filter_le (Eq b) _).trans ?_
  convert Polynomial.map_dvd f Polynomial.prod_multiset_X_sub_C_dvd p
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_apply,
    Polynomial.map_sub, map_X, map_C]

