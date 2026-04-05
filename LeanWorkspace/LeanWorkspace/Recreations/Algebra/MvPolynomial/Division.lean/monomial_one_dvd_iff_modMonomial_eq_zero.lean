import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem monomial_one_dvd_iff_modMonomial_eq_zero {i : σ →₀ ℕ} {x : MvPolynomial σ R} :
    monomial i (1 : R) ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ i = 0 := AddMonoidAlgebra.of'_dvd_iff_modOf_eq_zero

