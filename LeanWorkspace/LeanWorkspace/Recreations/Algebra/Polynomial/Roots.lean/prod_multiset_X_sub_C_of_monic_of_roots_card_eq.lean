import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp : p.Monic)
    (hroots : Multiset.card p.roots = p.natDegree) : (p.roots.map fun a => X - C a).prod = p := by
  convert Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  rw [hp.leadingCoeff, C_1, one_mul]

