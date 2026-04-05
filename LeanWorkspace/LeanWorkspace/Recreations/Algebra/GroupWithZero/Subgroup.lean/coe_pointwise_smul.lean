import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [Monoid M] [AddGroup A] [DistribMulAction M A] {a : M}

theorem coe_pointwise_smul (a : M) (S : AddSubgroup A) : ↑(a • S) = a • (S : Set A) := rfl

