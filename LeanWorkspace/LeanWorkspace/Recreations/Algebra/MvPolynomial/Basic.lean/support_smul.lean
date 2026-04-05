import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem support_smul {S₁ : Type*} [SMulZeroClass S₁ R] {a : S₁} {f : MvPolynomial σ R} :
    (a • f).support ⊆ f.support := Finsupp.support_smul

