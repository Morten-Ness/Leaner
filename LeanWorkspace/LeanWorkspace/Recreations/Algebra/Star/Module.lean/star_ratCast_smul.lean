import Mathlib

variable {R M : Type*}

theorem star_ratCast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : ℚ)
    (x : M) : star ((n : R) • x) = (n : R) • star x := map_ratCast_smul (starAddEquiv : M ≃+ M) _ _ _ x

