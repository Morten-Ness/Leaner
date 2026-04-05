import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable {M N μ r} [CovariantClass M N μ r]

theorem Group.mulLeftReflectLE_of_mulLeftMono [Group N] [LE N]
    [MulLeftMono N] : MulLeftReflectLE N := inferInstance

