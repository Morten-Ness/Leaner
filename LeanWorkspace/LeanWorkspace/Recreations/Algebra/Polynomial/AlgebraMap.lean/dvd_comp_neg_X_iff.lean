import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommRing R] {p : R[X]} {t : R}

theorem dvd_comp_neg_X_iff (p q : R[X]) : p ∣ q.comp (-Polynomial.X) ↔ p.comp (-Polynomial.X) ∣ q := by
  let _ := invertibleOne (α := R)
  let _ := invertibleNeg (R := R) 1
  simpa using Polynomial.dvd_comp_C_mul_X_add_C_iff p q (-1) 0

