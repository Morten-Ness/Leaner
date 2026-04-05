import Mathlib

open scoped Pointwise

variable {G G' P P' : Type*} [AddGroup G] [AddGroup G'] [AddTorsor G P] [AddTorsor G' P']

theorem snd_vadd (v : G × G') (p : P × P') : (v +ᵥ p).2 = v.2 +ᵥ p.2 := rfl

