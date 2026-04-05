import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

variable {L : Type w} [LieRing L] [LieAlgebra R L]

theorem lift_unique (f : X → L) (g : FreeLieAlgebra R X →ₗ⁅R⁆ L) : g ∘ FreeLieAlgebra.of R = f ↔ g = FreeLieAlgebra.lift R f := (FreeLieAlgebra.lift R).symm_apply_eq

