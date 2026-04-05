import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

theorem LieAlgebra.ad_apply (x y : L) : LieAlgebra.ad R L x y = ⁅x, y⁆ := rfl

