import Mathlib

variable {α M : Type*} [One M]

theorem hasFiniteMulSupport_one : Function.HasFiniteMulSupport fun _ : α ↦ (1 : M) := by
  classical
  simpa [Function.HasFiniteMulSupport] using (Set.toFinite (∅ : Set α))
