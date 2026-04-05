import Mathlib

variable {R M : Type*}

theorem star_inv_natCast_smul [DivisionSemiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M]
    (n : ℕ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x := map_inv_natCast_smul (starAddEquiv : M ≃+ M) R R n x

