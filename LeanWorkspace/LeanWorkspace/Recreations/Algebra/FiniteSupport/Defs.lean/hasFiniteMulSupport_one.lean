import Mathlib

variable {α M : Type*} [One M]

theorem hasFiniteMulSupport_one : Function.HasFiniteMulSupport fun _ : α ↦ (1 : M) := by
  simp [Function.HasFiniteMulSupport]

