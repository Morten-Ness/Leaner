import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vsub_self (p : P) : p -ᵥ p = (0 : G) := by
  rw [← zero_add (p -ᵥ p), ← vadd_vsub_assoc, vadd_vsub]

