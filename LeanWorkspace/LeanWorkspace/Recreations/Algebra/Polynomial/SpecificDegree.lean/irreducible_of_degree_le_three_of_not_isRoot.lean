import Mathlib

variable {K : Type*} [Field K] {p : K[X]}

theorem irreducible_of_degree_le_three_of_not_isRoot
    (hdeg : p.natDegree ∈ Finset.Icc 1 3) (hnot : ∀ x, ¬ IsRoot p x) :
    Irreducible p := by
  rw [Finset.mem_Icc] at hdeg
  by_cases hdeg2 : 2 ≤ p.natDegree
  · rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg2 hdeg.2]
    apply Multiset.eq_zero_of_forall_notMem
    simp_all
  · apply Polynomial.irreducible_of_degree_eq_one
    rw [← Nat.cast_one, Polynomial.degree_eq_iff_natDegree_eq_of_pos (by simp)]
    exact le_antisymm (by rwa [not_le, Nat.lt_succ_iff] at hdeg2) hdeg.1

