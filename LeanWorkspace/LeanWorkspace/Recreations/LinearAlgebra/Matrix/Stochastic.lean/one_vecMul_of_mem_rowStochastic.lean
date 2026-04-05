import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem one_vecMul_of_mem_rowStochastic (hM : M ∈ Matrix.rowStochastic R n) : M *ᵥ 1 = 1 := (Matrix.mem_rowStochastic.1 hM).2

