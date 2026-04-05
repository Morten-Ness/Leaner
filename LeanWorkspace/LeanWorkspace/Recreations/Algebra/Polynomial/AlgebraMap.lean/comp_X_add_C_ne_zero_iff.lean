import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommRing R] {p : R[X]} {t : R}

theorem comp_X_add_C_ne_zero_iff : p.comp (Polynomial.X + Polynomial.C t) ≠ 0 ↔ p ≠ 0 := Polynomial.comp_X_add_C_eq_zero_iff.not

