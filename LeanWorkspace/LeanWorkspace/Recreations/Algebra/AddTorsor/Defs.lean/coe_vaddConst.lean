import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

theorem coe_vaddConst (p : P) : ⇑(Equiv.vaddConst p) = fun v => v +ᵥ p := rfl

