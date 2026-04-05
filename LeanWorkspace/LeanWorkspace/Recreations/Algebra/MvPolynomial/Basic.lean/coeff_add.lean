import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_add (m : σ →₀ ℕ) (p q : MvPolynomial σ R) : MvPolynomial.coeff m (p + q) = MvPolynomial.coeff m p + MvPolynomial.coeff m q := add_apply p q m

