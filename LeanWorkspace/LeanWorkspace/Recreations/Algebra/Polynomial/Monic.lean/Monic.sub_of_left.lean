import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Ring R] {p : R[X]}

theorem Monic.sub_of_left {p q : R[X]} (hp : Polynomial.Monic p) (hpq : degree q < degree p) :
    Polynomial.Monic (p - q) := by
  rw [sub_eq_add_neg]
  apply hp.add_of_left
  rwa [Polynomial.degree_neg]

