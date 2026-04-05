import Mathlib

variable (M : Type*) [Monoid M]

variable (G : Type*) [Group G] [Fintype G]

variable (R : Type*) [CommRing R] [MulSemiringAction G R]

theorem prodXSubSMul.smul (x : R) (g : G) : g • prodXSubSMul G R x = prodXSubSMul G R x := letI := Classical.decEq R
  Finset.smul_prod'.trans <|
    Fintype.prod_bijective _ (MulAction.bijective g) _ _ fun g' ↦ by
      rw [ofQuotientStabilizer_smul, smul_sub, Polynomial.smul_X, Polynomial.smul_C]

