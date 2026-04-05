import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem support_C (c : R) [h : Decidable (c = 0)] :
    (MvPolynomial.C (σ := σ) c).support = if c = 0 then ∅ else {0} :=
  MvPolynomial.support_monomial

