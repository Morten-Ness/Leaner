import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_mul_le (i : σ) (f g : MvPolynomial σ R) :
    MvPolynomial.degreeOf i (f * g) ≤ MvPolynomial.degreeOf i f + MvPolynomial.degreeOf i g := by
  classical
  simp only [MvPolynomial.degreeOf]
  convert Multiset.count_le_of_le i MvPolynomial.degrees_mul_le
  rw [Multiset.count_add]

