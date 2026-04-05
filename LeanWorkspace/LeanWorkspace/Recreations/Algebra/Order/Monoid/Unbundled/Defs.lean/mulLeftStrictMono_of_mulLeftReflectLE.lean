import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (mu : N → N → N)

theorem mulLeftStrictMono_of_mulLeftReflectLE [Mul N] [LinearOrder N] [MulLeftReflectLE N] :
    MulLeftStrictMono N := inferInstance

