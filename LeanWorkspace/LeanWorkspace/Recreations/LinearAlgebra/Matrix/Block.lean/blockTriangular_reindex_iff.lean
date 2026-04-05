import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

variable [Zero R]

theorem blockTriangular_reindex_iff {b : n → α} {e : m ≃ n} :
    (reindex e e M).BlockTriangular b ↔ M.BlockTriangular (b ∘ e) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · convert h.submatrix
    simp only [reindex_apply, submatrix_submatrix, submatrix_id_id, Equiv.symm_comp_self]
  · convert h.submatrix
    simp only [comp_assoc b e e.symm, Equiv.self_comp_symm, comp_id]

