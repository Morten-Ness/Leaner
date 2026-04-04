import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem Coplanar.finiteDimensional_direction_affineSpan {s : Set P} (h : Coplanar k s) :
    FiniteDimensional k (affineSpan k s).direction := (direction_affineSpan k s).symm ▸ h.finiteDimensional_vectorSpan

