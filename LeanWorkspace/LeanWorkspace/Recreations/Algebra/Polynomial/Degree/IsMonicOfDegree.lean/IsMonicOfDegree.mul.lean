import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem IsMonicOfDegree.mul {p q : R[X]} {m n : ℕ} (hp : IsMonicOfDegree p m)
    (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p * q) (m + n) := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [Polynomial.isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hp hq ⊢
    exact ⟨hp, hq⟩
  refine ⟨?_, hp.monic.mul hq.monic⟩
  have : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    rw [hp.leadingCoeff_eq, hq.leadingCoeff_eq, one_mul]
    exact one_ne_zero
  rw [natDegree_mul' this, hp.natDegree_eq, hq.natDegree_eq]

