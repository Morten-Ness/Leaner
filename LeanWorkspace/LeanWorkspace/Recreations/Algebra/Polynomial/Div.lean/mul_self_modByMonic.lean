import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem mul_self_modByMonic (hq : q.Monic) : (p * q) %ₘ q = 0 := by
  rw [Polynomial.modByMonic_eq_zero_iff_dvd hq]
  exact dvd_mul_left q p

