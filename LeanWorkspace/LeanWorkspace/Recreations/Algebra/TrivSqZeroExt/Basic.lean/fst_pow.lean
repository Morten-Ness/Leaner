import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem fst_pow [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (x : tsze R M) (n : ℕ) : TrivSqZeroExt.fst (x ^ n) = x.fst ^ n := rfl

