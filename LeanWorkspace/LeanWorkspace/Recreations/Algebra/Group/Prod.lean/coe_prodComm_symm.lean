import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable [MulOneClass M] [MulOneClass N]

theorem coe_prodComm_symm : ⇑(MulEquiv.prodComm : M × N ≃* N × M).symm = Prod.swap := rfl

