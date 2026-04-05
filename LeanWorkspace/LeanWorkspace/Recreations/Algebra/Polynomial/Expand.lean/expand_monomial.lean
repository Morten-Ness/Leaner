import Mathlib

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_monomial (r : R) : Polynomial.expand R p (monomial q r) = monomial (q * p) r := by
  simp_rw [← smul_X_eq_monomial, map_smul, map_pow, Polynomial.expand_X, mul_comm, pow_mul]

