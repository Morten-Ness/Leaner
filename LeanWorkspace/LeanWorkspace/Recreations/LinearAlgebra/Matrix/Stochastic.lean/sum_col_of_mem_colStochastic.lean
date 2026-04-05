import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem sum_col_of_mem_colStochastic (hM : M ∈ Matrix.colStochastic R n) (i : n) : ∑ j, M j i = 1 := (Matrix.mem_colStochastic_iff_sum.1 hM).2 _

