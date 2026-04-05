import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [Monoid M] [AddGroup A] [DistribMulAction M A] {a : M}

theorem pointwise_smul_def (S : AddSubgroup A) :
    a • S = S.map (DistribMulAction.toAddMonoidEnd _ _ a) := rfl

