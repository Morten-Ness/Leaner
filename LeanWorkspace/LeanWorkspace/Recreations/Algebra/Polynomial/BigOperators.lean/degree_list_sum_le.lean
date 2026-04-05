import Mathlib

open scoped Polynomial

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable {S : Type*} [Semiring S]

theorem degree_list_sum_le (l : List S[X]) : degree l.sum ≤ (l.map natDegree).maximum := by
  apply Polynomial.degree_list_sum_le_of_forall_degree_le
  intro p hp
  by_cases h : p = 0
  · subst h
    simp
  · rw [degree_eq_natDegree h]
    apply List.le_maximum_of_mem'
    rw [List.mem_map]
    use p
    simp [hp]

