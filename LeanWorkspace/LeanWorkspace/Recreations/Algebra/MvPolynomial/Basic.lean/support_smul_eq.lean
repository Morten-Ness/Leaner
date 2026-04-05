import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem support_smul_eq {S : Type*} [Semiring S] [IsDomain S] [Module S R]
    [Module.IsTorsionFree S R] {a : S} (h : a ≠ 0) (p : MvPolynomial σ R) :
    (a • p).support = p.support := Finsupp.support_smul_eq h

