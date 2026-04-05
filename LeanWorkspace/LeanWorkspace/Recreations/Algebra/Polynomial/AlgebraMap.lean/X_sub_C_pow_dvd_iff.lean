import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommRing R] {p : R[X]} {t : R}

theorem X_sub_C_pow_dvd_iff {n : ℕ} : (Polynomial.X - Polynomial.C t) ^ n ∣ p ↔ Polynomial.X ^ n ∣ p.comp (Polynomial.X + Polynomial.C t) := by
  convert (map_dvd_iff <| Polynomial.algEquivAevalXAddC t).symm using 2
  simp [Polynomial.C_eq_algebraMap]

