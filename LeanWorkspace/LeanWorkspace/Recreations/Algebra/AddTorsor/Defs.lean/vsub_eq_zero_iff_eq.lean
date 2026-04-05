import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vsub_eq_zero_iff_eq {p₁ p₂ : P} : p₁ -ᵥ p₂ = (0 : G) ↔ p₁ = p₂ := Iff.intro eq_of_vsub_eq_zero fun h => h ▸ vsub_self _

