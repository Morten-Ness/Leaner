import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem X_mul_cancel_left_iff {i : σ} :
    MvPolynomial.X i * p = MvPolynomial.X i * q ↔ p = q := MvPolynomial.monomial_one_mul_cancel_left_iff

