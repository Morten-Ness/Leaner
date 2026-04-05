import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem mul_X_divMonomial (x : MvPolynomial σ R) (i : σ) :
    x * X i /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x := MvPolynomial.divMonomial_mul_monomial _ _

