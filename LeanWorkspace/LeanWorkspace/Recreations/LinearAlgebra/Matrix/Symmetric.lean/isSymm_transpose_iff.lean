import Mathlib

variable {α β n m R : Type*}

theorem isSymm_transpose_iff {A : Matrix n n α} : Aᵀ.IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.transpose)⟩
  rw [← A.transpose_transpose]
  exact h.transpose

