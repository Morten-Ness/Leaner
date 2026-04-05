import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Ring R] {p : R[X]}

theorem Monic.sub_of_right {p q : R[X]} (hq : q.leadingCoeff = -1) (hpq : degree p < degree q) :
    Polynomial.Monic (p - q) := by
  have : (-q).coeff (-q).natDegree = 1 := by
    rw [natDegree_neg, coeff_neg, show q.coeff q.natDegree = -1 from hq, neg_neg]
  rw [sub_eq_add_neg]
  apply Polynomial.Monic.add_of_right this
  rwa [Polynomial.degree_neg]

