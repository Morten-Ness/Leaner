import Mathlib

variable (α β : Type*) [LinearOrderedCommGroupWithZero α] [LinearOrderedCommGroupWithZero β]

theorem fst_comp_inl : (fst _ _).comp (inl α β) = .id α := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp

