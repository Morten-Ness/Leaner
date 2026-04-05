import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem coeff_eq_zero_of_totalDegree_lt {f : MvPolynomial σ R} {d : σ →₀ ℕ}
    (h : f.totalDegree < ∑ i ∈ d.support, d i) : coeff d f = 0 := by
  classical
    rw [MvPolynomial.totalDegree, Finset.sup_lt_iff] at h
    · specialize h d
      rw [mem_support_iff] at h
      refine not_not.mp (mt h ?_)
      exact lt_irrefl _
    · exact lt_of_le_of_lt (Nat.zero_le _) h

