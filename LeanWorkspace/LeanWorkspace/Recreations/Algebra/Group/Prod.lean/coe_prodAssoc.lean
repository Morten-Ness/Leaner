import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable [MulOneClass M] [MulOneClass N]

variable [MulOneClass P]

theorem coe_prodAssoc : ⇑(MulEquiv.prodAssoc : (M × N) × P ≃* M × (N × P)) = Equiv.prodAssoc M N P := rfl

