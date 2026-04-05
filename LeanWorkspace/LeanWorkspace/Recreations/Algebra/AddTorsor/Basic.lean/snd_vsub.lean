import Mathlib

open scoped Pointwise

variable {G G' P P' : Type*} [AddGroup G] [AddGroup G'] [AddTorsor G P] [AddTorsor G' P']

theorem snd_vsub (p₁ p₂ : P × P') : (p₁ -ᵥ p₂ : G × G').2 = p₁.2 -ᵥ p₂.2 := rfl

