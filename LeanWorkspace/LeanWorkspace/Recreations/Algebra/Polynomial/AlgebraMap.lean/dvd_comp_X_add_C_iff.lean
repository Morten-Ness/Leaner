import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommRing R] {p : R[X]} {t : R}

theorem dvd_comp_X_add_C_iff (p q : R[X]) (a : R) :
    p ∣ q.comp (Polynomial.X + Polynomial.C a) ↔ p.comp (Polynomial.X - Polynomial.C a) ∣ q := by
  simpa using Polynomial.dvd_comp_X_sub_C_iff p q (-a)

