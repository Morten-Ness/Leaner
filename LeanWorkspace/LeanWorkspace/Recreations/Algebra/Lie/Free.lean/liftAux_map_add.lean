import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

variable {L : Type w} [LieRing L] [LieAlgebra R L]

theorem liftAux_map_add (f : X → L) (a b : lib R X) :
    FreeLieAlgebra.liftAux R f (a + b) = FreeLieAlgebra.liftAux R f a + FreeLieAlgebra.liftAux R f b := map_add _ a b

