import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vadd_vsub (g : G) (p : P) : (g +ᵥ p) -ᵥ p = g := AddTorsor.vadd_vsub' g p

