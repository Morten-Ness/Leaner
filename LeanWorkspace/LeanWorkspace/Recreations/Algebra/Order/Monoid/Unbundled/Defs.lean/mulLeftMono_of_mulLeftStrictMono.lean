import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

theorem mulLeftMono_of_mulLeftStrictMono (M) [Mul M] [PartialOrder M] [MulLeftStrictMono M] :
    MulLeftMono M := covariantClass_le_of_lt _ _ _

