import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem X_ne_zero [Nontrivial R] (s : σ) :
    MvPolynomial.X (R := R) s ≠ 0 := by
  rw [MvPolynomial.ne_zero_iff]
  use Finsupp.single s 1
  simp only [MvPolynomial.coeff_X, ne_eq, one_ne_zero, not_false_eq_true]

