import Mathlib

variable {α β n m R : Type*}

theorem isSymm_smul_iff [Monoid R] [MulAction R α] {A : Matrix n n α} (k : R) [Invertible k] :
    (k • A).IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.smul k)⟩
  rw [← invOf_smul_smul k A]
  exact h.smul ⅟k

