import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_add_le_iff_left {n : ℕ} (p q : R[X]) (qn : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ p.natDegree ≤ n := by
  refine ⟨fun h => ?_, fun h => natDegree_add_le_of_degree_le h qn⟩
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
  convert Polynomial.natDegree_le_iff_coeff_eq_zero.mp h m hm using 1
  rw [coeff_add, Polynomial.natDegree_le_iff_coeff_eq_zero.mp qn _ hm, add_zero]

