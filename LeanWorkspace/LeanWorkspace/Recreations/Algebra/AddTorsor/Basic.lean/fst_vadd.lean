import Mathlib

open scoped Pointwise

variable {G G' P P' : Type*} [AddGroup G] [AddGroup G'] [AddTorsor G P] [AddTorsor G' P']

theorem fst_vadd (v : G × G') (p : P × P') : (v +ᵥ p).1 = v.1 +ᵥ p.1 := rfl

