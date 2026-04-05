import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

theorem LieSubmodule.coe_toEnd_pow (N : LieSubmodule R L M) (x : L) (y : N) (n : ℕ) :
    ((toEnd R L N x ^ n) y : M) = (toEnd R L M x ^ n) y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, ih, LieSubmodule.coe_toEnd]

