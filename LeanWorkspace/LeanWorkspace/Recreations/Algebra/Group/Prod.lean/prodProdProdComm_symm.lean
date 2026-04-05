import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable [MulOneClass M] [MulOneClass N]

variable [MulOneClass P]

variable {M' : Type*} {N' : Type*} [MulOneClass N'] [MulOneClass M']

theorem prodProdProdComm_symm : (MulEquiv.prodProdProdComm M N M' N').symm = MulEquiv.prodProdProdComm M M' N N' := rfl

