import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_mul_X_self (j : σ) (f : MvPolynomial σ R) :
    MvPolynomial.degreeOf j (f * X j) ≤ MvPolynomial.degreeOf j f + 1 := by
  classical
  simp only [MvPolynomial.degreeOf]
  apply (Multiset.count_le_of_le j MvPolynomial.degrees_mul_le).trans
  simp only [Multiset.count_add, add_le_add_iff_left]
  convert Multiset.count_le_of_le j <| MvPolynomial.degrees_X' j
  rw [Multiset.count_singleton_self]

