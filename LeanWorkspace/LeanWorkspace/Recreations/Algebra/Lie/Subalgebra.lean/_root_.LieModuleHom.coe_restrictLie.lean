import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

variable {M : Type w} [AddCommGroup M] [LieRingModule L M]

variable {N : Type w₁} [AddCommGroup N] [LieRingModule L N] [Module R N]

variable [Module R M]

theorem _root_.LieModuleHom.coe_restrictLie (f : M →ₗ⁅R,L⁆ N) : ⇑(f.restrictLie L') = f := rfl

