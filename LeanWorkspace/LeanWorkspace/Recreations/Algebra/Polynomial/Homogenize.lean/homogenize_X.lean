import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_X {n : ℕ} (hn : n ≠ 0) : Polynomial.homogenize (X : R[X]) n = .X 0 * .X 1 ^ (n - 1) := by
  rw [← pow_one X, Polynomial.homogenize_X_pow, pow_one]
  rwa [Nat.one_le_iff_ne_zero]

