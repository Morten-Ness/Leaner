import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable {M' : Type*} {N' : Type*} [Mul M] [Mul N] [Mul M'] [Mul N'] [Mul P] (f : M →ₙ* M')
  (g : N →ₙ* N')

theorem coe_prodMap : ⇑(MulHom.prodMap f g) = Prod.map f g := rfl

