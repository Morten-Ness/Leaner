import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem IsMonicOfDegree.of_mul_left {p q : R[X]} {m n : ℕ} (hp : IsMonicOfDegree p m)
    (hpq : IsMonicOfDegree (p * q) (m + n)) :
    IsMonicOfDegree q n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [Polynomial.isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hpq ⊢
    exact hpq.2
  have h₂ : q.Monic := hp.monic.of_mul_monic_left hpq.monic
  refine ⟨?_, h₂⟩
  have := hpq.natDegree_eq
  have h : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    rw [hp.leadingCoeff_eq, h₂.leadingCoeff, one_mul]
    exact one_ne_zero
  rw [natDegree_mul' h, hp.natDegree_eq] at this
  exact (Nat.add_left_cancel this.symm).symm

