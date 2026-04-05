import Mathlib

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendScalars_η :
    letI := f.toAlgebra
    dsimp% η (extendScalars f) = (AlgebraTensorModule.rid R S S).toModuleIso.hom := rfl

