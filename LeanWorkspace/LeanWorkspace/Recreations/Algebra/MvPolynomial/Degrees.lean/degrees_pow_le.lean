import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_pow_le {p : MvPolynomial σ R} {n : ℕ} : (p ^ n).degrees ≤ n • p.degrees := by
  simpa using MvPolynomial.degrees_prod_le (s := .range n) (f := fun _ ↦ p)

