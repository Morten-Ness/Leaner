import Mathlib

variable {M M₂ : Type*}

theorem map_nnrat_smul [AddCommMonoid M] [AddCommMonoid M₂]
    [_instM : Module ℚ≥0 M] [_instM₂ : Module ℚ≥0 M₂]
    {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂]
    (f : F) (c : ℚ≥0) (x : M) : f (c • x) = c • f x := map_nnratCast_smul f ℚ≥0 ℚ≥0 c x

