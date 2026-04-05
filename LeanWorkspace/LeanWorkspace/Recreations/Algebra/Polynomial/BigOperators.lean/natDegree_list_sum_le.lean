import Mathlib

open scoped Polynomial

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable {S : Type*} [Semiring S]

theorem natDegree_list_sum_le (l : List S[X]) :
    natDegree l.sum ≤ (l.map natDegree).foldr max 0 := by
  apply List.sum_le_foldr_max natDegree
  · simp
  · exact natDegree_add_le

