import Mathlib

variable {M N α β : Type*}

theorem AddMonoidHom.coe_toMultiplicativeLeft [AddZeroClass α] [MulOneClass β] (f : α →+ Additive β) :
    ⇑(toMultiplicativeLeft f) = toMul ∘ f ∘ toAdd := rfl

