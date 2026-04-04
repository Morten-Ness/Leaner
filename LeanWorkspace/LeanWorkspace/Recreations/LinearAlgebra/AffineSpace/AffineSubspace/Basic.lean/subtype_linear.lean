import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem subtype_linear (s : AffineSubspace k P) [Nonempty s] :
    s.subtype.linear = s.direction.subtype := rfl

