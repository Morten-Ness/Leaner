import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem sum_mulVec_of_mem_colStochastic {M : Matrix n n R} {x : n → R}
    (hA : M ∈ Matrix.colStochastic R n) : ∑ i, (M *ᵥ x) i = ∑ i, x i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp [Matrix.sum_col_of_mem_colStochastic hA, ← Finset.sum_mul]

