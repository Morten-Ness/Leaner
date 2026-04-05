import Mathlib

variable {R M M₁ : Type*} [AddCommMonoid M] [AddCommMonoid M₁]

theorem range_smulRight_apply [DivisionSemiring R] [Module R M] [Module R M₁]
    {f : M →ₗ[R] R} (hf : f ≠ 0) (x : M₁) :
    range (f.smulRight x) = Submodule.span R {x} := LinearMap.range_smulRight_apply_of_surjective (f.surjective hf) x

