import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_one [DecidableEq σ] (m) : MvPolynomial.coeff m (1 : MvPolynomial σ R) = if 0 = m then 1 else 0 := MvPolynomial.coeff_C m 1

