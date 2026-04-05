import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem le_one_of_mem_colStochastic (hM : M ∈ Matrix.colStochastic R n) {i j : n} :
    M j i ≤ 1 := by
  rw [← Matrix.sum_col_of_mem_colStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 k _) (mem_univ j)

