import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem _root_.IsRegular.monomial {m : σ →₀ ℕ} {a : R}
    (ha : IsRegular a) :
    IsRegular (MvPolynomial.monomial m a) := by
  rw [← isLeftRegular_iff_isRegular]
  intro p q h
  ext d
  have h' := congr_arg (MvPolynomial.coeff (m + d)) h
  simp only [MvPolynomial.coeff_monomial_mul] at h'
  rw [← ha.left.eq_iff, h']

