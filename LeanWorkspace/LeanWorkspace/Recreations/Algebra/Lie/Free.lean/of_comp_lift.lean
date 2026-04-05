import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

variable {L : Type w} [LieRing L] [LieAlgebra R L]

theorem of_comp_lift (f : X → L) : FreeLieAlgebra.lift R f ∘ FreeLieAlgebra.of R = f := (FreeLieAlgebra.lift R).left_inv f

