import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_add_of_natDegree_lt_left {p q : R[X]} (pq : q.natDegree < p.natDegree) :
    (p + q).eraseLead = p.eraseLead + q := Polynomial.eraseLead_add_of_degree_lt_left (degree_lt_degree pq)

