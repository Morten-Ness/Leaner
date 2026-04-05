import Mathlib

variable {R : Type u}

variable [NonUnitalNonAssocRing R] {a b c : R}

theorem sub_left : Commute a c → Commute b c → Commute (a - b) c := SemiconjBy.sub_left

