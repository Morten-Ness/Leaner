import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem divMonomial_zero (x : MvPolynomial σ R) : x /ᵐᵒⁿᵒᵐⁱᵃˡ 0 = x := x.divOf_zero

