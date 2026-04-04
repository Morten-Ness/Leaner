import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem finiteDimensional_direction_affineSpan_of_finite {s : Set P} (h : Set.Finite s) :
    FiniteDimensional k (affineSpan k s).direction := (direction_affineSpan k s).symm ▸ finiteDimensional_vectorSpan_of_finite k h

