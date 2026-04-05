import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem binomial_eq_binomial {k l m n : ℕ} {u v : R} (hu : u ≠ 0) (hv : v ≠ 0) :
    Polynomial.C u * Polynomial.X ^ k + Polynomial.C v * Polynomial.X ^ l = Polynomial.C u * Polynomial.X ^ m + Polynomial.C v * Polynomial.X ^ n ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u + v = 0 ∧ k = l ∧ m = n := by
  simp_rw [Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.toFinsupp_inj, Polynomial.toFinsupp_add, Polynomial.toFinsupp_monomial]
  exact Finsupp.single_add_single_eq_single_add_single hu hv

