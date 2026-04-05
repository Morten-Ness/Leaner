import Mathlib

open scoped Pointwise

variable {G G' P P' : Type*} [AddGroup G] [AddGroup G'] [AddTorsor G P] [AddTorsor G' P']

theorem mk_vsub_mk (p₁ p₂ : P) (p₁' p₂' : P') :
    ((p₁, p₁') -ᵥ (p₂, p₂') : G × G') = (p₁ -ᵥ p₂, p₁' -ᵥ p₂') := rfl

