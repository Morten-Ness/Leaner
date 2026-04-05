import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem monomial_add_single : MvPolynomial.monomial (s + Finsupp.single n e) a = MvPolynomial.monomial s a * MvPolynomial.X n ^ e := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, mul_one]

