import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_monomial [DecidableEq σ] (m n) (a) :
    MvPolynomial.coeff m (MvPolynomial.monomial n a : MvPolynomial σ R) = if n = m then a else 0 := Finsupp.single_apply

