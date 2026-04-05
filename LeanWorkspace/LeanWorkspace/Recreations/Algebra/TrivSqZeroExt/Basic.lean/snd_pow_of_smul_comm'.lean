import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_pow_of_smul_comm' [Monoid R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (x : tsze R M) (n : ℕ)
    (h : x.snd <• x.fst = x.fst •> x.snd) : TrivSqZeroExt.snd (x ^ n) = n • (x.snd <• x.fst ^ n.pred) := by
  rw [TrivSqZeroExt.snd_pow_of_smul_comm _ _ h, TrivSqZeroExt.snd_pow_of_smul_comm.aux _ h]

