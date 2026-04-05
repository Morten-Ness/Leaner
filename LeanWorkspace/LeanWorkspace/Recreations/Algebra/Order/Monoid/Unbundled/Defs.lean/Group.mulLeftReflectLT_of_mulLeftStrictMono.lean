import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable {M N μ r} [CovariantClass M N μ r]

theorem Group.mulLeftReflectLT_of_mulLeftStrictMono [Group N] [LT N]
    [MulLeftStrictMono N] : MulLeftReflectLT N := inferInstance

