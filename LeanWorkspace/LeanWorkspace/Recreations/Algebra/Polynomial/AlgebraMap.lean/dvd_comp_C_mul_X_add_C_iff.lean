import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommRing R] {p : R[X]} {t : R}

theorem dvd_comp_C_mul_X_add_C_iff (p q : R[X]) (a b : R) [Invertible a] :
    p ∣ q.comp (Polynomial.C a * Polynomial.X + Polynomial.C b) ↔ p.comp (Polynomial.C ⅟a * (Polynomial.X - Polynomial.C b)) ∣ q := by
  convert map_dvd_iff <| Polynomial.algEquivCMulXAddC a b using 2
  simp [← Polynomial.comp_eq_aeval, comp_assoc, ← mul_assoc, ← C_mul]

