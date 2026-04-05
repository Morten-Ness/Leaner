import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable {M N μ r} [CovariantClass M N μ r]

theorem Group.mulRightReflectLE_of_mulRightMono [Group N] [LE N]
    [MulRightMono N] : MulRightReflectLE N := inferInstance

