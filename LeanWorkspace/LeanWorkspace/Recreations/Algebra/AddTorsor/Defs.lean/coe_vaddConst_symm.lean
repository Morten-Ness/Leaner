import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

theorem coe_vaddConst_symm (p : P) : ⇑(Equiv.vaddConst p).symm = fun p' => p' -ᵥ p := rfl

