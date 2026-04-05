import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_sum_le {ι : Type*} (i : σ) (s : Finset ι) (f : ι → MvPolynomial σ R) :
    MvPolynomial.degreeOf i (∑ j ∈ s, f j) ≤ s.sup fun j => MvPolynomial.degreeOf i (f j) := by
  simp_rw [MvPolynomial.degreeOf_eq_sup]
  exact supDegree_sum_le

