import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem IsMonicOfDegree.of_mul_right {p q : R[X]} {m n : ℕ} (hq : IsMonicOfDegree q n)
    (hpq : IsMonicOfDegree (p * q) (m + n)) :
    IsMonicOfDegree p m := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [Polynomial.isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hpq ⊢
    exact hpq.1
  have h₂ : p.Monic := hq.monic.of_mul_monic_right hpq.monic
  refine ⟨?_, h₂⟩
  have := hpq.natDegree_eq
  have h : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    rw [h₂.leadingCoeff, hq.leadingCoeff_eq, one_mul]
    exact one_ne_zero
  rw [natDegree_mul' h, hq.natDegree_eq] at this
  exact (Nat.add_right_cancel this.symm).symm

