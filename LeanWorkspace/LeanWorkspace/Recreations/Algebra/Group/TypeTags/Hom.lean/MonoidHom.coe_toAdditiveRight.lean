import Mathlib

variable {M N α β : Type*}

theorem MonoidHom.coe_toAdditiveRight [AddZeroClass α] [MulOneClass β] (f : Multiplicative α →* β) :
    ⇑(toAdditiveRight f) = ofMul ∘ f ∘ ofAdd := rfl

