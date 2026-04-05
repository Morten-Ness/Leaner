import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_monomial_mul' (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    MvPolynomial.coeff m (MvPolynomial.monomial s r * p) = if s ≤ m then r * MvPolynomial.coeff (m - s) p else 0 := by
  -- note that if we allow `R` to be non-commutative we will have to duplicate the proof above.
  rw [mul_comm, mul_comm r]
  exact MvPolynomial.coeff_mul_monomial' _ _ _ _

