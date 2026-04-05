import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [Monoid M] [AddGroup A] [DistribMulAction M A] {a : M}

theorem pointwise_smul_toAddSubmonoid (a : M) (S : AddSubgroup A) :
    (a • S).toAddSubmonoid = a • S.toAddSubmonoid := rfl

