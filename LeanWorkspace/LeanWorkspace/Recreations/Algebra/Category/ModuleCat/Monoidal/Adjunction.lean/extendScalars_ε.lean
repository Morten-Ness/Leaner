import Mathlib

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendScalars_ε :
    letI := f.toAlgebra
    dsimp% ε (extendScalars f) = (AlgebraTensorModule.rid R S S).toModuleIso.inv := rfl

