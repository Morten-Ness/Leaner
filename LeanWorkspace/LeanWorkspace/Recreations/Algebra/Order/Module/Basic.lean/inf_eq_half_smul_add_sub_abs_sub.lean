import Mathlib

variable {𝕜 R M : Type*}

variable [Semiring R] [Invertible (2 : R)] [Lattice M] [AddCommGroup M] [Module R M]
  [IsOrderedAddMonoid M]

theorem inf_eq_half_smul_add_sub_abs_sub (x y : M) : x ⊓ y = (⅟2 : R) • (x + y - |y - x|) := by
  rw [← two_nsmul_inf_eq_add_sub_abs_sub x y, two_smul, ← two_smul R,
    smul_smul, invOf_mul_self, one_smul]

