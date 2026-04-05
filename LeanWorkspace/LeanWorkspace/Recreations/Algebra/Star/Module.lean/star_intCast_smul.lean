import Mathlib

variable {R M : Type*}

theorem star_intCast_smul [Ring R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : ℤ)
    (x : M) : star ((n : R) • x) = (n : R) • star x := map_intCast_smul (starAddEquiv : M ≃+ M) R R n x

