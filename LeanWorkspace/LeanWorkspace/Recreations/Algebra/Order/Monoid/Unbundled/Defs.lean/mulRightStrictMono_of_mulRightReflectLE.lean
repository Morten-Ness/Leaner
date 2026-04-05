import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (mu : N → N → N)

theorem mulRightStrictMono_of_mulRightReflectLE [Mul N] [LinearOrder N] [MulRightReflectLE N] :
    MulRightStrictMono N := inferInstance

