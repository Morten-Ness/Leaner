import Mathlib

open scoped Pointwise

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vsub_right_cancel_iff {p₁ p₂ p : P} : p -ᵥ p₁ = p -ᵥ p₂ ↔ p₁ = p₂ := ⟨vsub_right_cancel, fun h => h ▸ rfl⟩

