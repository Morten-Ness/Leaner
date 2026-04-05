import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_pow_le (i : σ) (p : MvPolynomial σ R) (n : ℕ) :
    MvPolynomial.degreeOf i (p ^ n) ≤ n * MvPolynomial.degreeOf i p := by
  simpa using MvPolynomial.degreeOf_prod_le i (Finset.range n) (fun _ => p)

