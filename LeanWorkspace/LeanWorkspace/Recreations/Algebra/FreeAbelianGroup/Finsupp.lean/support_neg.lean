import Mathlib

variable {X : Type*}

theorem support_neg (a : FreeAbelianGroup X) : FreeAbelianGroup.support (-a) = FreeAbelianGroup.support a := by
  simp only [FreeAbelianGroup.support, map_neg, Finsupp.support_neg]

