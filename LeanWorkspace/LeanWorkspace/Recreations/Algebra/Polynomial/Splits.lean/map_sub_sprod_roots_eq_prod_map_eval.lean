import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem map_sub_sprod_roots_eq_prod_map_eval
    (s : Multiset R) (g : R[X]) (hg : g.Monic) (hg' : g.Splits) :
    ((s ×ˢ g.roots).map fun ij ↦ ij.1 - ij.2).prod = (s.map g.eval).prod := by
  have := hg'.eq_prod_roots
  rw [hg.leadingCoeff, map_one, one_mul] at this
  conv_rhs => rw [this]
  simp_rw [eval_multiset_prod, Multiset.prod_map_product_eq_prod_prod, Multiset.map_map]
  congr! with x hx
  ext; simp

