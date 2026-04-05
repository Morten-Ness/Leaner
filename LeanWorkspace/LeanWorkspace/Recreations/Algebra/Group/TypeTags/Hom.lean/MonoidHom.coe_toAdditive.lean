import Mathlib

variable {M N α β : Type*}

theorem MonoidHom.coe_toAdditive [MulOneClass α] [MulOneClass β] (f : α →* β) :
    ⇑(toAdditive f) = ofMul ∘ f ∘ toMul := rfl

