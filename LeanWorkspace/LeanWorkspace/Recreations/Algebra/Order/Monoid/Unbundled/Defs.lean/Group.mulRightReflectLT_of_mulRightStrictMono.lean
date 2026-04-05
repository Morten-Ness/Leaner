import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable {M N μ r} [CovariantClass M N μ r]

theorem Group.mulRightReflectLT_of_mulRightStrictMono [Group N] [LT N]
    [MulRightStrictMono N] : MulRightReflectLT N := inferInstance

