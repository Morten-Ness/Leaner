import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem C_leadingCoeff_mul_prod_multiset_X_sub_C (hroots : Multiset.card p.roots = p.natDegree) :
    C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p := (eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (Polynomial.monic_multisetProd_X_sub_C p.roots)
      Polynomial.prod_multiset_X_sub_C_dvd p
      ((natDegree_multiset_prod_X_sub_C_eq_card _).trans hroots).ge).symm

