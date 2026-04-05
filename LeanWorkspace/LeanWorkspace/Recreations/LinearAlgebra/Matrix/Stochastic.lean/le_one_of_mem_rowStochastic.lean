import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem le_one_of_mem_rowStochastic (hM : M ∈ Matrix.rowStochastic R n) {i j : n} :
    M i j ≤ 1 := by
  rw [← Matrix.sum_row_of_mem_rowStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)

