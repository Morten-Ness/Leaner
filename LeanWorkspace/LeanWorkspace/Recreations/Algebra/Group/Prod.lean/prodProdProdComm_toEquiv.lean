import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable [MulOneClass M] [MulOneClass N]

variable [MulOneClass P]

variable {M' : Type*} {N' : Type*} [MulOneClass N'] [MulOneClass M']

theorem prodProdProdComm_toEquiv :
    (MulEquiv.prodProdProdComm M N M' N' : _ ≃ _) = Equiv.prodProdProdComm M N M' N' := rfl

