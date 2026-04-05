import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem X_divMonomial (i : σ) : (X i : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 1 := MvPolynomial.divMonomial_monomial (Finsupp.single i 1)

