import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem zero_divMonomial (s : σ →₀ ℕ) : (0 : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 := AddMonoidAlgebra.zero_divOf _

