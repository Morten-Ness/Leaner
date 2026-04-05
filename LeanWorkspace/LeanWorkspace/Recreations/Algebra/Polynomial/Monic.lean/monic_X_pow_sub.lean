import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Ring R] {p : R[X]}

theorem monic_X_pow_sub {n : ℕ} (H : degree p < n) : Polynomial.Monic (Polynomial.X ^ n - p) := by
  simpa [sub_eq_add_neg] using Polynomial.monic_X_pow_add (show degree (-p) < n by rwa [← Polynomial.degree_neg p] at H)

