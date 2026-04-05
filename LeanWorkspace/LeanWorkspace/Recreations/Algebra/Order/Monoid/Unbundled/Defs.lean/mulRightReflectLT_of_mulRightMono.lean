import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (mu : N → N → N)

theorem mulRightReflectLT_of_mulRightMono [Mul N] [LinearOrder N] [MulRightMono N] :
    MulRightReflectLT N := inferInstance

