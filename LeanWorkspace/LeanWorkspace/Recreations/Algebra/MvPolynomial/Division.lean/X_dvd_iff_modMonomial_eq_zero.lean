import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem X_dvd_iff_modMonomial_eq_zero {i : σ} {x : MvPolynomial σ R} :
    X i ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 := MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero

