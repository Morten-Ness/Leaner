import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem mul_X_modMonomial (x : MvPolynomial σ R) (i : σ) :
    x * X i %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 := MvPolynomial.mul_monomial_modMonomial _ _

