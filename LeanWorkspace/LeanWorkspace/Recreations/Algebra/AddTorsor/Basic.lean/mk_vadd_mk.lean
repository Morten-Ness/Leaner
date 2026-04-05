import Mathlib

open scoped Pointwise

variable {G G' P P' : Type*} [AddGroup G] [AddGroup G'] [AddTorsor G P] [AddTorsor G' P']

theorem mk_vadd_mk (v : G) (v' : G') (p : P) (p' : P') : (v, v') +ᵥ (p, p') = (v +ᵥ p, v' +ᵥ p') := rfl

