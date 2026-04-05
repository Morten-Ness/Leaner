import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (mu : N → N → N)

theorem mulRightReflectLE_of_mulLeftReflectLE [CommSemigroup N] [LE N] [MulLeftReflectLE N] :
    MulRightReflectLE N := inferInstance

