import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

variable {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N'] [MulOneClass P]
  (f : M →* M') (g : N →* N')

theorem coe_prodMap : ⇑(MonoidHom.prodMap f g) = Prod.map f g := rfl

