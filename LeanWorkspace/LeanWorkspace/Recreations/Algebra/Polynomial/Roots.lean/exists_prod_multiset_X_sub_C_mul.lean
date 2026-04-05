import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem exists_prod_multiset_X_sub_C_mul (p : R[X]) :
    ∃ q,
      (p.roots.map fun a => X - C a).prod * q = p ∧
        Multiset.card p.roots + q.natDegree = p.natDegree ∧ q.roots = 0 := by
  obtain ⟨q, he⟩ := Polynomial.prod_multiset_X_sub_C_dvd p
  use q, he.symm
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero] at he
    subst he
    simp
  constructor
  · conv_rhs => rw [he]
    rw [(Polynomial.monic_multisetProd_X_sub_C p.roots).natDegree_mul' hq,
      natDegree_multiset_prod_X_sub_C_eq_card]
  · replace he := congr_arg Polynomial.roots he.symm
    rw [Polynomial.roots_mul, Polynomial.roots_multiset_prod_X_sub_C] at he
    exacts [add_eq_left.1 he, mul_ne_zero (Polynomial.monic_multisetProd_X_sub_C p.roots).ne_zero hq]

