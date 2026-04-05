import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeffs_one : MvPolynomial.coeffs (1 : MvPolynomial σ R) ⊆ {1} := by
  classical
    rw [MvPolynomial.coeffs, Finset.image_subset_iff]
    simp_all [MvPolynomial.coeff_one]

