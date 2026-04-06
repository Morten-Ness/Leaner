import Mathlib

variable {X : Type*}

theorem support_zero : FreeAbelianGroup.support (0 : FreeAbelianGroup X) = ∅ := by
  simp [FreeAbelianGroup.support]
