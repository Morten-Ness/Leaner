import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (mu : N → N → N)

theorem mulRightReflectLT_of_mulLeftReflectLT [CommSemigroup N] [LT N] [MulLeftReflectLT N] :
    MulRightReflectLT N := inferInstance

