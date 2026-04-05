import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem X_injective [Nontrivial R] : Function.Injective (MvPolynomial.X : σ → MvPolynomial σ R) := (MvPolynomial.monomial_left_injective one_ne_zero).comp (Finsupp.single_left_injective one_ne_zero)

