import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_pow_eq_sum [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (x : tsze R M) (n : ℕ) :
    TrivSqZeroExt.snd (x ^ n) = ((List.range n).map fun i => x.fst ^ (n.pred - i) •> x.snd <• x.fst ^ i).sum := rfl

