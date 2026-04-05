import Mathlib

variable {α M : Type*} [One M]

theorem hasFiniteMulSupport_fun_one : HasFiniteMulSupport (1 : α → M) := by
  simp [HasFiniteMulSupport]

