import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_add_of_degree_lt_left {p q : R[X]} (pq : q.degree < p.degree) :
    (p + q).eraseLead = p.eraseLead + q := by
  ext n
  by_cases nd : n = p.natDegree
  · rw [nd, Polynomial.eraseLead_coeff, if_pos (natDegree_add_eq_left_of_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le pq Polynomial.degree_le_natDegree)).symm
  · rw [Polynomial.eraseLead_coeff, coeff_add, coeff_add, Polynomial.eraseLead_coeff, if_neg, if_neg nd]
    rintro rfl
    exact nd (natDegree_add_eq_left_of_degree_lt pq)

