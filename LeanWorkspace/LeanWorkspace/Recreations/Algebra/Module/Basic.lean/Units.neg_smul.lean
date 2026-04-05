import Mathlib

variable {α R M M₂ : Type*}

theorem Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u : Rˣ) (x : M) :
    -u • x = -(u • x) := by
  rw [Units.smul_def, Units.val_neg, _root_.neg_smul, Units.smul_def]

