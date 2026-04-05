import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem ext_iff_degree_le {p q : R[X]} {n : ℕ} (hp : p.degree ≤ n) (hq : q.degree ≤ n) :
    p = q ↔ ∀ i ≤ n, p.coeff i = q.coeff i := Polynomial.ext_iff_natDegree_le (natDegree_le_of_degree_le hp) (natDegree_le_of_degree_le hq)

