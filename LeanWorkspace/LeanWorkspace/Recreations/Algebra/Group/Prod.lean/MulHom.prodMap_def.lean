import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable {M' : Type*} {N' : Type*} [Mul M] [Mul N] [Mul M'] [Mul N'] [Mul P] (f : M →ₙ* M')
  (g : N →ₙ* N')

theorem prodMap_def : MulHom.prodMap f g = (f.comp (MulHom.fst M N)).prod (g.comp (MulHom.snd M N)) := rfl

