import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem X_mul_divMonomial (i : σ) (x : MvPolynomial σ R) :
    X i * x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x := MvPolynomial.divMonomial_monomial_mul _ _

