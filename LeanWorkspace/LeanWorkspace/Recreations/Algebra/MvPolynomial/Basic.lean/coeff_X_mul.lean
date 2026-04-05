import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_X_mul (m) (s : σ) (p : MvPolynomial σ R) :
    MvPolynomial.coeff (Finsupp.single s 1 + m) (MvPolynomial.X s * p) = MvPolynomial.coeff m p := (MvPolynomial.coeff_monomial_mul _ _ _ _).trans (one_mul _)

