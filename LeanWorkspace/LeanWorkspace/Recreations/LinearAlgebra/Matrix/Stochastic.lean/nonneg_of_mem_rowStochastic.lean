import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem nonneg_of_mem_rowStochastic (hM : M ∈ Matrix.rowStochastic R n) {i j : n} : 0 ≤ M i j := hM.1 _ _

