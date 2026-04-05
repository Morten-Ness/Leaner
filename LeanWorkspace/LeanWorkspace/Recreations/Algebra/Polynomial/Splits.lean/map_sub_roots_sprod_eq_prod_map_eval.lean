import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem map_sub_roots_sprod_eq_prod_map_eval
    (s : Multiset R) (g : R[X]) (hg : g.Monic) (hg' : g.Splits) :
    ((g.roots ×ˢ s).map fun ij ↦ ij.1 - ij.2).prod =
      (-1) ^ (s.card * g.roots.card) * (s.map g.eval).prod := by
  trans ((s ×ˢ g.roots).map fun ij ↦ (-1) * (ij.1 - ij.2)).prod
  · rw [← Multiset.map_swap_product, Multiset.map_map]; simp
  · rw [Multiset.prod_map_mul]; simp [Polynomial.map_sub_sprod_roots_eq_prod_map_eval _ _ hg hg']

