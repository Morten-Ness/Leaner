import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

variable {L : Type w} [LieRing L] [LieAlgebra R L]

theorem liftAux_map_smul (f : X → L) (t : R) (a : lib R X) :
    FreeLieAlgebra.liftAux R f (t • a) = t • FreeLieAlgebra.liftAux R f a := map_smul _ t a

