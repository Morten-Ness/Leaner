import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem one_vecMul_of_mem_colStochastic (hM : M ∈ Matrix.colStochastic R n) : 1 ᵥ* M = 1 := (Matrix.mem_colStochastic.1 hM).2

