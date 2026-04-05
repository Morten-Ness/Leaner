import Mathlib

variable {M N α β : Type*}

theorem Additive.addMonoidHom_ext [MulOneClass α] [AddZeroClass β]
    (f g : Additive α →+ β) (h : f.toMultiplicativeRight = g.toMultiplicativeRight) : f = g := AddMonoidHom.toMultiplicativeRight.injective h

