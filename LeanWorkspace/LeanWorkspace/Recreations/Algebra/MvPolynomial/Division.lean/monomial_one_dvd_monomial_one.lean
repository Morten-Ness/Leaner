import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem monomial_one_dvd_monomial_one [Nontrivial R] {i j : σ →₀ ℕ} :
    monomial i (1 : R) ∣ monomial j 1 ↔ i ≤ j := by
  rw [MvPolynomial.monomial_dvd_monomial]
  simp_rw [one_ne_zero, false_or, dvd_rfl, and_true]

