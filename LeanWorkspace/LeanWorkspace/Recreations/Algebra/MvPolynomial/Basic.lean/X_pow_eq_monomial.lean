import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem X_pow_eq_monomial : MvPolynomial.X n ^ e = MvPolynomial.monomial (Finsupp.single n e) (1 : R) := by
  simp [MvPolynomial.X, MvPolynomial.monomial_pow]

