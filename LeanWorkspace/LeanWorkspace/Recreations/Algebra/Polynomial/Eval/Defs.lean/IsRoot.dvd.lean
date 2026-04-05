import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem IsRoot.dvd {R : Type*} [CommSemiring R] {p q : R[X]} {x : R} (h : p.IsRoot x)
    (hpq : p ∣ q) : q.IsRoot x := by
  rwa [Polynomial.IsRoot, Polynomial.eval, Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hpq]

