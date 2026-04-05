import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem disjoint_support_monomial {a : σ →₀ ℕ} {p : MvPolynomial σ R} {s : R}
    (ha : a ∉ p.support) (hs : s ≠ 0) : Disjoint (MvPolynomial.monomial a s).support p.support := by
  classical
  simpa [MvPolynomial.support_monomial, hs] using MvPolynomial.notMem_support_iff.mp ha

