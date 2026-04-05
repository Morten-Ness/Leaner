import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_mul_X (m) (s : σ) (p : MvPolynomial σ R) :
    MvPolynomial.coeff (m + Finsupp.single s 1) (p * MvPolynomial.X s) = MvPolynomial.coeff m p := (MvPolynomial.coeff_mul_monomial _ _ _ _).trans (mul_one _)

