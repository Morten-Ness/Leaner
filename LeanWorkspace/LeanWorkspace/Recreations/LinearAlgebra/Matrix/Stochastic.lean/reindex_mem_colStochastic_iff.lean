import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem reindex_mem_colStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ ∈ Matrix.colStochastic R m ↔ M ∈ Matrix.colStochastic R n := by
  rw [← transpose_transpose (reindex e₁ e₂ M), transpose_reindex,
    Matrix.transpose_mem_colStochastic_iff_mem_rowStochastic, Matrix.reindex_mem_rowStochastic_iff,
    ← Matrix.transpose_mem_colStochastic_iff_mem_rowStochastic, transpose_transpose]

