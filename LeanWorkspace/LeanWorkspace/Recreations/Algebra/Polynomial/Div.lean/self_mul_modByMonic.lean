import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem self_mul_modByMonic (hq : q.Monic) : (q * p) %ₘ q = 0 := by
  rw [Polynomial.modByMonic_eq_zero_iff_dvd hq]
  exact dvd_mul_right q p

