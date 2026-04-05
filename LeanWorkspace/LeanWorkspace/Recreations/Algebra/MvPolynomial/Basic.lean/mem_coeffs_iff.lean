import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem mem_coeffs_iff {p : MvPolynomial σ R} {c : R} :
    c ∈ p.coeffs ↔ ∃ n ∈ p.support, c = p.coeff n := by
  simp [MvPolynomial.coeffs, eq_comm, (Finset.mem_image)]

