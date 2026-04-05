import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem Splits.dvd_of_roots_le_roots (hp : f.Splits) (hp0 : f ≠ 0) (hq : f.roots ≤ g.roots) :
    f ∣ g := by
  rw [hp.eq_prod_roots, C_mul_dvd (leadingCoeff_ne_zero.2 hp0)]
  exact (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hq)).trans
    (prod_multiset_X_sub_C_dvd _)

