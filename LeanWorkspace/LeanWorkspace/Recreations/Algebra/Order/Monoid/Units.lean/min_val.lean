import Mathlib

variable {α : Type*}

theorem min_val [Monoid α] [LinearOrder α] (a b : αˣ) : (min a b).val = min a.val b.val := by
  simp_rw [min_def, Units.val_le_val, ← apply_ite]
  rfl

