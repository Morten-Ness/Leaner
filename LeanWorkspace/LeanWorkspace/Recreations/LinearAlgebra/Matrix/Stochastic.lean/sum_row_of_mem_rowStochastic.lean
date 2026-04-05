import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem sum_row_of_mem_rowStochastic (hM : M ∈ Matrix.rowStochastic R n) (i : n) : ∑ j, M i j = 1 := (Matrix.mem_rowStochastic_iff_sum.1 hM).2 _

