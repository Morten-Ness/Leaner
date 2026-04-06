import Mathlib

variable {X : Type*}

theorem support_neg (a : FreeAbelianGroup X) : FreeAbelianGroup.support (-a) = FreeAbelianGroup.support a := by
  ext x
  simp [FreeAbelianGroup.support]
