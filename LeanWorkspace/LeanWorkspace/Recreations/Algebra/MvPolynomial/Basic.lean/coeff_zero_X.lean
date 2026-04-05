import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_zero_X (i : σ) : MvPolynomial.coeff 0 (MvPolynomial.X i : MvPolynomial σ R) = 0 := single_eq_of_ne' fun h => by cases Finsupp.single_eq_zero.1 h

