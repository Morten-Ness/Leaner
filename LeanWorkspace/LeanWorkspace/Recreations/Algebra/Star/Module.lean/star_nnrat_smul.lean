import Mathlib

variable {R M : Type*}

theorem star_nnrat_smul [AddCommMonoid R] [StarAddMonoid R] [Module ℚ≥0 R] (q : ℚ≥0) (x : R) :
    star (q • x) = q • star x := map_nnrat_smul (starAddEquiv : R ≃+ R) _ _

