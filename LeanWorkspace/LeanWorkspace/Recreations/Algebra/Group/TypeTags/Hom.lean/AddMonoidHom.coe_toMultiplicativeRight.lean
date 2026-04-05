import Mathlib

variable {M N α β : Type*}

theorem AddMonoidHom.coe_toMultiplicativeRight [MulOneClass α] [AddZeroClass β]
    (f : Additive α →+ β) : ⇑(toMultiplicativeRight f) = ofAdd ∘ f ∘ ofMul := rfl

