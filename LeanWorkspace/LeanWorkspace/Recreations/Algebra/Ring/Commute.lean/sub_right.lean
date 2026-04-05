import Mathlib

variable {R : Type u}

variable [NonUnitalNonAssocRing R] {a b c : R}

theorem sub_right : Commute a b → Commute a c → Commute a (b - c) := SemiconjBy.sub_right

