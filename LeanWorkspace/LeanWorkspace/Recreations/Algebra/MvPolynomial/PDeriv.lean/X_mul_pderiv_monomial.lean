import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem X_mul_pderiv_monomial {i : σ} {m : σ →₀ ℕ} {r : R} :
    X i * MvPolynomial.pderiv i (monomial m r) = m i • monomial m r := by
  rw [MvPolynomial.pderiv_monomial, X, monomial_mul, smul_monomial]
  by_cases h : m i = 0
  · simp_rw [h, Nat.cast_zero, mul_zero, zero_smul, monomial_zero]
  rw [one_mul, mul_comm, nsmul_eq_mul, add_comm, sub_add_single_one_cancel h]

