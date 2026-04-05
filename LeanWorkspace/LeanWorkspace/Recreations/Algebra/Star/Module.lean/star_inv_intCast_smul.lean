import Mathlib

variable {R M : Type*}

theorem star_inv_intCast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M]
    (n : ℤ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x := map_inv_intCast_smul (starAddEquiv : M ≃+ M) R R n x

