import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem IsMonicOfDegree.add_right {p q : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n)
    (hq : q.natDegree < n) :
    IsMonicOfDegree (p + q) n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  refine (Polynomial.isMonicOfDegree_iff ..).mpr ⟨?_, ?_⟩
  · exact natDegree_add_le_of_degree_le hp.natDegree_eq.le hq.le
  · rw [coeff_add_eq_left_of_lt hq]
    exact ((Polynomial.isMonicOfDegree_iff p n).mp hp).2

