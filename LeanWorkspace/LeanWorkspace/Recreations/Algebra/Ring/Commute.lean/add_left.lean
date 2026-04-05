import Mathlib

variable {R : Type u}

theorem add_left [Distrib R] {a b c : R} : Commute a c → Commute b c → Commute (a + b) c := SemiconjBy.add_left
-- for some reason mathport expected `Semiring` instead of `Distrib`?

