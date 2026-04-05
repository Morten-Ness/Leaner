import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_add_of_natDegree_lt_right {p q : R[X]} (pq : p.natDegree < q.natDegree) :
    (p + q).eraseLead = p + q.eraseLead := Polynomial.eraseLead_add_of_degree_lt_right (degree_lt_degree pq)

