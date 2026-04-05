import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem X_dvd_monomial {i : σ} {j : σ →₀ ℕ} {r : R} :
    (X i : MvPolynomial σ R) ∣ monomial j r ↔ r = 0 ∨ j i ≠ 0 := by
  refine MvPolynomial.monomial_dvd_monomial.trans ?_
  simp_rw [one_dvd, and_true, Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]

