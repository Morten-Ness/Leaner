import Mathlib

open scoped Pointwise

variable {G G' P P' : Type*} [AddGroup G] [AddGroup G'] [AddTorsor G P] [AddTorsor G' P']

theorem fst_vsub (p₁ p₂ : P × P') : (p₁ -ᵥ p₂ : G × G').1 = p₁.1 -ᵥ p₂.1 := rfl

