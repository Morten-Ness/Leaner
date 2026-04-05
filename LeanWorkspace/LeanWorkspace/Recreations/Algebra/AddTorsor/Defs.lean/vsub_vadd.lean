import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vsub_vadd (p₁ p₂ : P) : (p₁ -ᵥ p₂) +ᵥ p₂ = p₁ := AddTorsor.vsub_vadd' p₁ p₂

