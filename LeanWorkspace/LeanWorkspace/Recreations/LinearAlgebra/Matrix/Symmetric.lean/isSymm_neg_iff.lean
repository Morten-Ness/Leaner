import Mathlib

variable {α β n m R : Type*}

theorem isSymm_neg_iff [InvolutiveNeg α] {A : Matrix n n α} : (-A).IsSymm ↔ A.IsSymm := by
  refine ⟨fun h ↦ ?_, (·.neg)⟩
  rw [← neg_neg A]
  exact h.neg

