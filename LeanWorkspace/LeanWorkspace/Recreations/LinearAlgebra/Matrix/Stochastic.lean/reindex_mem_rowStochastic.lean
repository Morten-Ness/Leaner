import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem reindex_mem_rowStochastic {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} (hM : M ∈ Matrix.rowStochastic R n) : M.reindex e₁ e₂ ∈ Matrix.rowStochastic R m := ⟨fun _ _ ↦ by simpa using Matrix.nonneg_of_mem_rowStochastic hM, by simp [submatrix_mulVec_equiv, hM.2]⟩

