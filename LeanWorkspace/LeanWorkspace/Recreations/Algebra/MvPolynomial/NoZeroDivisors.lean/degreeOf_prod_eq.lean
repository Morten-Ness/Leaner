import Mathlib

variable {R : Type*}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R]

variable {p q : MvPolynomial σ R}

variable [NoZeroDivisors R]

theorem degreeOf_prod_eq {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R)
    (h : ∀ i ∈ s, f i ≠ 0) :
    degreeOf n (∏ i ∈ s, f i) = ∑ i ∈ s, degreeOf n (f i) := by
  rcases subsingleton_or_nontrivial (MvPolynomial σ R) with nontrivial | nontrivial
  · simp [Subsingleton.eq_zero]
  · classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s a_not_mem ih =>
      simp only [mem_insert, ne_eq, forall_eq_or_imp] at h
      obtain ⟨ha, hs⟩ := h
      simp [a_not_mem, not_false_eq_true, prod_insert, Finset.sum_insert, MvPolynomial.degreeOf_mul_eq ha
        (by rw [prod_ne_zero_iff]; exact hs), ih hs]

