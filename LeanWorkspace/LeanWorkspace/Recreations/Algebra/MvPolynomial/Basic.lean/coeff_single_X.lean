import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_single_X [DecidableEq σ] (s s' : σ) (n : ℕ) :
    (MvPolynomial.X s).coeff (R := R) (Finsupp.single s' n) = if n = 1 ∧ s = s' then 1 else 0 := by
  simpa [eq_comm, and_comm] using MvPolynomial.coeff_single_X_pow s s' 1 n

