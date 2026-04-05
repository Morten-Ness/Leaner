import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [AddGroup α] [StarAddMonoid α]

theorem isHermitian_neg_iff {A : Matrix n n α} : (-A).IsHermitian ↔ A.IsHermitian := by
  refine ⟨fun h ↦ ?_, (·.neg)⟩
  rw [← neg_neg A]
  exact h.neg

