import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {S} {T : Submonoid M}

theorem coe_submonoidMap_apply (e : M ≃* N) (S : Submonoid M) (g : S) :
    ((MulEquiv.submonoidMap e S g : S.map (e : M →* N)) : N) = e g := rfl

