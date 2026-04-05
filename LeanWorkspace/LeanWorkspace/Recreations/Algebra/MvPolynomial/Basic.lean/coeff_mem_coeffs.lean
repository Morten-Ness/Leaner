import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_mem_coeffs {p : MvPolynomial σ R} (m : σ →₀ ℕ)
    (h : p.coeff m ≠ 0) : p.coeff m ∈ p.coeffs := letI := Classical.decEq R
  Finset.mem_image_of_mem p.coeff (MvPolynomial.mem_support_iff.mpr h)

