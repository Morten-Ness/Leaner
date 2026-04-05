import Mathlib

variable {M N α β : Type*}

theorem MonoidHom.coe_toAdditiveLeft [MulOneClass α] [AddZeroClass β] (f : α →* Multiplicative β) :
    ⇑(toAdditiveLeft f) = toAdd ∘ f ∘ toMul := rfl

