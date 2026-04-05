import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem X_dvd_sub_C : Polynomial.X ∣ p - Polynomial.C (p.coeff 0) := by
  simp [Polynomial.X_dvd_iff, coeff_C]

