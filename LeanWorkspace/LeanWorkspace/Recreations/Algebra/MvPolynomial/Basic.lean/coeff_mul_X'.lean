import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_mul_X' [DecidableEq σ] (m) (s : σ) (p : MvPolynomial σ R) :
    MvPolynomial.coeff m (p * MvPolynomial.X s) = if s ∈ m.support then MvPolynomial.coeff (m - Finsupp.single s 1) p else 0 := by
  refine (MvPolynomial.coeff_mul_monomial' _ _ _ _).trans ?_
  simp_rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.succ_le_iff, pos_iff_ne_zero,
    mul_one]

