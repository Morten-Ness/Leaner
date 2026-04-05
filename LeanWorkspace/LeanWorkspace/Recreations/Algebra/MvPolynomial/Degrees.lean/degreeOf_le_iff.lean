import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_le_iff {n : σ} {f : MvPolynomial σ R} {d : ℕ} :
    MvPolynomial.degreeOf n f ≤ d ↔ ∀ m ∈ support f, m n ≤ d := by
  rw [MvPolynomial.degreeOf_eq_sup, Finset.sup_le_iff]

