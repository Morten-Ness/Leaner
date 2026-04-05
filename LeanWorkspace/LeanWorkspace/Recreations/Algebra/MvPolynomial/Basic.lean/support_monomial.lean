import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem support_monomial [h : Decidable (a = 0)] :
    (MvPolynomial.monomial s a).support = if a = 0 then ∅ else {s} := by
  rw [← Subsingleton.elim (Classical.decEq R a 0) h]
  rfl

