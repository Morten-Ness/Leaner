import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem modMonomial_X (i : σ) : (X i : MvPolynomial σ R) %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 := MvPolynomial.monomial_modMonomial _

