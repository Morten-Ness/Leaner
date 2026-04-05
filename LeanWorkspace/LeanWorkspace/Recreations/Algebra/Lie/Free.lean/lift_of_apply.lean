import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

variable {L : Type w} [LieRing L] [LieAlgebra R L]

theorem lift_of_apply (f : X → L) (x) : FreeLieAlgebra.lift R f (FreeLieAlgebra.of R x) = f x := by
  rw [← @Function.comp_apply _ _ _ (FreeLieAlgebra.lift R f) (FreeLieAlgebra.of R) x, FreeLieAlgebra.of_comp_lift]

