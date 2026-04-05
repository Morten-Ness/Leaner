import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem prod_X_pow_eq_monomial : ∏ x ∈ s.support, MvPolynomial.X x ^ s x = MvPolynomial.monomial s (1 : R) := by
  simp only [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod]

