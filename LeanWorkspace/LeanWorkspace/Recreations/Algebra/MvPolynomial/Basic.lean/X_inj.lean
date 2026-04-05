import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem X_inj [Nontrivial R] (m n : σ) : MvPolynomial.X m = (MvPolynomial.X n : MvPolynomial σ R) ↔ m = n := MvPolynomial.X_injective.eq_iff

