import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem monomial_mul {s s' : σ →₀ ℕ} {a b : R} :
    MvPolynomial.monomial s a * MvPolynomial.monomial s' b = MvPolynomial.monomial (s + s') (a * b) := AddMonoidAlgebra.single_mul_single ..

