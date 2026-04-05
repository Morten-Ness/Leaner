import Mathlib

variable {X : Type*}

theorem notMem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∉ a.support ↔ FreeAbelianGroup.coeff x a = 0 := by
  rw [FreeAbelianGroup.support, Finsupp.notMem_support_iff]
  exact Iff.rfl

