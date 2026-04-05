import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_X (i : σ) : MvPolynomial.coeff (Finsupp.single i 1) (MvPolynomial.X i : MvPolynomial σ R) = 1 := by
  classical rw [MvPolynomial.coeff_X', if_pos rfl]

