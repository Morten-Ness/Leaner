import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁) (P : Type w₂)

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

variable [Module R M] [Module R N] [Module R P]

variable [LieRingModule L M] [LieRingModule L N] [LieRingModule L P]

variable [LieAlgebra R L] [LieModule R L N]

theorem coe_smul (t : R) (f : M →ₗ⁅R,L⁆ N) : ⇑(t • f) = t • (⇑f) := rfl

