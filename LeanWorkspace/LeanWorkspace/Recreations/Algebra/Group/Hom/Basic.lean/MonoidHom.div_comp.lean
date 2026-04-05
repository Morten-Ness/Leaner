import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOneClass M] [MulOneClass N] [CommGroup G] [CommGroup H]

theorem div_comp (f g : N →* G) (h : M →* N) : (f / g).comp h = f.comp h / g.comp h := rfl

