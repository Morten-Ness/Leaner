import Mathlib

variable {α β n m R : Type*}

theorem isSymm_reindex_iff {A : Matrix n n α} (f : n ≃ m) : (A.reindex f f).IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.reindex f)⟩
  simpa using h.reindex f.symm

