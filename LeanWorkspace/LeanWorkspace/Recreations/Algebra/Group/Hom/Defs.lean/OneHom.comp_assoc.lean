import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem OneHom.comp_assoc {Q : Type*} [One M] [One N] [One P] [One Q]
    (f : OneHom M N) (g : OneHom N P) (h : OneHom P Q) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

