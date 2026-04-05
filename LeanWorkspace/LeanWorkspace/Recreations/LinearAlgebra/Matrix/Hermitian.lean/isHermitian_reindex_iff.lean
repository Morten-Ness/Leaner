import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Star α] [Star β]

theorem isHermitian_reindex_iff {A : Matrix n n α} (f : n ≃ m) :
    (A.reindex f f).IsHermitian ↔ A.IsHermitian := by
  refine ⟨fun h ↦ ?_, (·.reindex f)⟩
  simpa using h.reindex f.symm

