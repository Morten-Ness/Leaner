FAIL
import Mathlib

variable {X : Type*}

theorem mem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∈ a.support ↔ FreeAbelianGroup.coeff x a ≠ 0 := by
  change (FreeAbelianGroup.toFinsupp a) x ≠ 0 ↔ FreeAbelianGroup.coeff x a ≠ 0
  rw [FreeAbelianGroup.coeff]
  rfl
