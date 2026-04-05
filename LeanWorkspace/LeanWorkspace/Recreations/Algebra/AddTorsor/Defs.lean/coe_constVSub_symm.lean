import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

theorem coe_constVSub_symm (p : P) : ⇑(Equiv.constVSub p).symm = fun (v : G) => -v +ᵥ p := rfl

