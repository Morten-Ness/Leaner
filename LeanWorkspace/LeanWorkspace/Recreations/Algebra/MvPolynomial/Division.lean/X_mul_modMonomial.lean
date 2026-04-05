import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem X_mul_modMonomial (i : σ) (x : MvPolynomial σ R) :
    X i * x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 := MvPolynomial.monomial_mul_modMonomial _ _

