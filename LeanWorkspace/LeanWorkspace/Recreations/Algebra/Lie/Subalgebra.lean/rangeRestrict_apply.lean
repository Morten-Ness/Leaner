import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

theorem rangeRestrict_apply (x : L) : f.rangeRestrict x = ⟨f x, LieHom.mem_range_self f x⟩ := rfl

