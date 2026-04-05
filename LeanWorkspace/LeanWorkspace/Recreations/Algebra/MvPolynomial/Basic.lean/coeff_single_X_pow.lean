import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_single_X_pow [DecidableEq σ] (s s' : σ) (n n' : ℕ) :
    (MvPolynomial.X (R := R) s ^ n).coeff (Finsupp.single s' n')
    = if s = s' ∧ n = n' ∨ n = 0 ∧ n' = 0 then 1 else 0 := by
  simp only [MvPolynomial.coeff_X_pow, single_eq_single_iff]

