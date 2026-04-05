import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_add_of_degree_lt_right {p q : R[X]} (pq : p.degree < q.degree) :
    (p + q).eraseLead = p + q.eraseLead := by
  ext n
  by_cases nd : n = q.natDegree
  · rw [nd, Polynomial.eraseLead_coeff, if_pos (natDegree_add_eq_right_of_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le pq Polynomial.degree_le_natDegree)).symm
  · rw [Polynomial.eraseLead_coeff, coeff_add, coeff_add, Polynomial.eraseLead_coeff, if_neg, if_neg nd]
    rintro rfl
    exact nd (natDegree_add_eq_right_of_degree_lt pq)

