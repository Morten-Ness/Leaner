import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_pow [CommMonoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [IsCentralScalar R M] (x : tsze R M) (n : ℕ) : TrivSqZeroExt.snd (x ^ n) = n • x.fst ^ n.pred • x.snd := TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _)

