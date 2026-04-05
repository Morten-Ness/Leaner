import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem monomial_modMonomial (s : σ →₀ ℕ) : monomial s (1 : R) %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 := AddMonoidAlgebra.of'_modOf _

