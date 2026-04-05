import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable (M N) [MulOneClass M] [MulOneClass N]

variable {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N'] [MulOneClass P]
  (f : M →* M') (g : N →* N')

theorem prodMap_def : MonoidHom.prodMap f g = (f.comp (MonoidHom.fst M N)).prod (g.comp (MonoidHom.snd M N)) := rfl

