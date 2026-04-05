import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem map_monomial (s : σ →₀ ℕ) (a : R) : MvPolynomial.map f (monomial s a) = monomial s (f a) := (MvPolynomial.eval₂_monomial _ _).trans monomial_eq.symm

