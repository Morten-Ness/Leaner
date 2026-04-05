import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem modByMonic_one (p : R[X]) : p %ₘ 1 = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd (by convert Polynomial.monic_one (R := R))).2 (one_dvd _)

