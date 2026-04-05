import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem transpose_mem_colStochastic_iff_mem_rowStochastic :
    Mᵀ ∈ Matrix.colStochastic R n ↔ M ∈ Matrix.rowStochastic R n := by
  simp only [Matrix.mem_colStochastic_iff_sum, Matrix.mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ ↦ forall_comm

