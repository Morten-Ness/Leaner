import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

variable {L : Type w} [LieRing L] [LieAlgebra R L]

theorem lift_comp_of (F : FreeLieAlgebra R X →ₗ⁅R⁆ L) : FreeLieAlgebra.lift R (F ∘ FreeLieAlgebra.of R) = F := by
  rw [← FreeLieAlgebra.lift_symm_apply]; exact (FreeLieAlgebra.lift R).apply_symm_apply F

