import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_sum_le {ι : Type*} [DecidableEq σ] (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (∑ i ∈ s, f i).degrees ≤ s.sup fun i => (f i).degrees := by
  simp_rw [MvPolynomial.degrees_def]; exact supDegree_sum_le

