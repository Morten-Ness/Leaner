import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vadd_right_cancel_iff {g₁ g₂ : G} (p : P) : g₁ +ᵥ p = g₂ +ᵥ p ↔ g₁ = g₂ := ⟨vadd_right_cancel p, fun h => h ▸ rfl⟩

