import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem eq_vadd_iff_vsub_eq (p₁ : P) (g : G) (p₂ : P) : p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g := ⟨fun h => h.symm ▸ vadd_vsub _ _, fun h => h ▸ (vsub_vadd _ _).symm⟩

