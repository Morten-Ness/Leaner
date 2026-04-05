import Mathlib

variable {M M₂ : Type*}

theorem map_rat_smul [AddCommGroup M] [AddCommGroup M₂]
    [_instM : Module ℚ M] [_instM₂ : Module ℚ M₂]
    {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂]
    (f : F) (c : ℚ) (x : M) : f (c • x) = c • f x := map_ratCast_smul f ℚ ℚ c x

