import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem IsMonicOfDegree.comp {p q : R[X]} {m n : ℕ} (hn : n ≠ 0) (hp : IsMonicOfDegree p m)
    (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p.comp q) (m * n) := by
  rcases subsingleton_or_nontrivial R with h | h
  · simp only [Polynomial.isMonicOfDegree_iff_of_subsingleton, mul_eq_zero] at hp ⊢
    exact .inl hp
  rw [← hp.natDegree_eq, ← hq.natDegree_eq]
  refine (Polynomial.isMonicOfDegree_iff ..).mpr ⟨natDegree_comp_le, ?_⟩
  rw [coeff_comp_degree_mul_degree (hq.natDegree_eq ▸ hn), hp.leadingCoeff_eq, hq.leadingCoeff_eq,
    one_pow, one_mul]

