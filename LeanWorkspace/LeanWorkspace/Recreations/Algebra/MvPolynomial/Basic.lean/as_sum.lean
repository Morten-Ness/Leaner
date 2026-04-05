import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem as_sum (p : MvPolynomial σ R) : p = ∑ v ∈ p.support, MvPolynomial.monomial v (MvPolynomial.coeff v p) := (MvPolynomial.support_sum_monomial_coeff p).symm

