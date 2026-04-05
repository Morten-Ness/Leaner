import Mathlib

variable {M N α β : Type*}

theorem Multiplicative.monoidHom_ext [AddZeroClass α] [MulOneClass β]
    (f g : Multiplicative α →* β) (h : f.toAdditiveRight = g.toAdditiveRight) : f = g := MonoidHom.toAdditiveRight.injective h

