import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (mu : N → N → N)

theorem mulLeftReflectLT_of_mulLeftMono [Mul N] [LinearOrder N] [MulLeftMono N] :
    MulLeftReflectLT N := inferInstance

