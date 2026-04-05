import Mathlib

section

variable {M N α β : Type*}

theorem Additive.addMonoidHom_ext [MulOneClass α] [AddZeroClass β]
    (f g : Additive α →+ β) (h : f.toMultiplicativeRight = g.toMultiplicativeRight) : f = g := AddMonoidHom.toMultiplicativeRight.injective h

end

section

variable {M N α β : Type*}

theorem Multiplicative.monoidHom_ext [AddZeroClass α] [MulOneClass β]
    (f g : Multiplicative α →* β) (h : f.toAdditiveRight = g.toAdditiveRight) : f = g := MonoidHom.toAdditiveRight.injective h

end
