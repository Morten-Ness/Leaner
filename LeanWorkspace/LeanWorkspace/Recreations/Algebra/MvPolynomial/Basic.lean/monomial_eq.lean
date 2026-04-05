import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem monomial_eq : MvPolynomial.monomial s a = MvPolynomial.C a * (s.prod fun n e => MvPolynomial.X n ^ e : MvPolynomial σ R) := by
  simp only [MvPolynomial.X_pow_eq_monomial, ← MvPolynomial.monomial_finsupp_sum_index, Finsupp.sum_single]

