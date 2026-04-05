import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable [MulOneClass M] [MulOneClass N]

variable [MulOneClass P]

theorem coe_prodAssoc_symm :
    ⇑(MulEquiv.prodAssoc : (M × N) × P ≃* M × (N × P)).symm = (Equiv.prodAssoc M N P).symm := rfl

