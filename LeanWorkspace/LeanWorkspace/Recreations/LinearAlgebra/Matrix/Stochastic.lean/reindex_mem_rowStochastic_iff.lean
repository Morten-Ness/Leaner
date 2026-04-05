import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem reindex_mem_rowStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ ∈ Matrix.rowStochastic R m ↔ M ∈ Matrix.rowStochastic R n := by
  refine ⟨fun h => ?_, Matrix.reindex_mem_rowStochastic⟩
  have : M = (M.reindex e₁ e₂).reindex e₁.symm e₂.symm := by simp
  rw [this]
  exact Matrix.reindex_mem_rowStochastic h

