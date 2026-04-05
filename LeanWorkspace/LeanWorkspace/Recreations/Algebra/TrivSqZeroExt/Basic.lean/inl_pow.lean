import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem inl_pow [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] (r : R)
    (n : ℕ) : (TrivSqZeroExt.inl r ^ n : tsze R M) = TrivSqZeroExt.inl (r ^ n) := TrivSqZeroExt.ext rfl <| by simp [TrivSqZeroExt.snd_pow_eq_sum, List.map_const']

