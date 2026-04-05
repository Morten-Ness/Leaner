import Mathlib

open scoped Pointwise

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vsub_left_cancel_iff {p₁ p₂ p : P} : p₁ -ᵥ p = p₂ -ᵥ p ↔ p₁ = p₂ := ⟨vsub_left_cancel, fun h => h ▸ rfl⟩

