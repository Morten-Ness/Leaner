import Mathlib

variable {α : Type*}

theorem max_val [Monoid α] [LinearOrder α] (a b : αˣ) : (max a b).val = max a.val b.val := by
  simp_rw [max_def, Units.val_le_val, ← apply_ite]
  rfl

