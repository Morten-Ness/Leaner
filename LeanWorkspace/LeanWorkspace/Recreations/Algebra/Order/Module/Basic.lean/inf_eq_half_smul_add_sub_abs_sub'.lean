import Mathlib

variable {𝕜 R M : Type*}

variable [DivisionSemiring 𝕜] [NeZero (2 : 𝕜)] [Lattice M] [AddCommGroup M] [Module 𝕜 M]
  [IsOrderedAddMonoid M]

theorem inf_eq_half_smul_add_sub_abs_sub' (x y : M) : x ⊓ y = (2⁻¹ : 𝕜) • (x + y - |y - x|) := let := invertibleOfNonzero (two_ne_zero' 𝕜); inf_eq_half_smul_add_sub_abs_sub 𝕜 x y

