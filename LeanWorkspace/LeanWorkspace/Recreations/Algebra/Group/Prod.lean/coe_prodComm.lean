import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable [MulOneClass M] [MulOneClass N]

theorem coe_prodComm : ⇑(MulEquiv.prodComm : M × N ≃* N × M) = Prod.swap := rfl

