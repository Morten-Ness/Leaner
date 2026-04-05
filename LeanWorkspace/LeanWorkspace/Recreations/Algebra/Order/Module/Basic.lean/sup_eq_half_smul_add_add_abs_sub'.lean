import Mathlib

variable {𝕜 R M : Type*}

variable [DivisionSemiring 𝕜] [NeZero (2 : 𝕜)] [Lattice M] [AddCommGroup M] [Module 𝕜 M]
  [IsOrderedAddMonoid M]

theorem sup_eq_half_smul_add_add_abs_sub' (x y : M) : x ⊔ y = (2⁻¹ : 𝕜) • (x + y + |y - x|) := let := invertibleOfNonzero (two_ne_zero' 𝕜); sup_eq_half_smul_add_add_abs_sub 𝕜 x y

