import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

theorem coe_range : (f.range : Set L₂) = Set.range f := LinearMap.coe_range (f : L →ₗ[R] L₂)

