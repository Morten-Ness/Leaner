import Mathlib

variable {R M : Type*}

theorem star_natCast_smul [Semiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M] (n : ℕ)
    (x : M) : star ((n : R) • x) = (n : R) • star x := map_natCast_smul (starAddEquiv : M ≃+ M) R R n x

