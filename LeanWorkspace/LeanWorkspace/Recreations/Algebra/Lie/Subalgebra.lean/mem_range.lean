import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

theorem mem_range (x : L₂) : x ∈ f.range ↔ ∃ y : L, f y = x := LinearMap.mem_range

