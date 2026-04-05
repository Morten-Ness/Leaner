import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

theorem mulRightMono_of_mulRightStrictMono (M) [Mul M] [PartialOrder M] [MulRightStrictMono M] :
    MulRightMono M := covariantClass_le_of_lt _ _ _

