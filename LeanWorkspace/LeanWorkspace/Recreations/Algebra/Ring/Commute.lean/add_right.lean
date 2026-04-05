import Mathlib

variable {R : Type u}

theorem add_right [Distrib R] {a b c : R} : Commute a b → Commute a c → Commute a (b + c) := SemiconjBy.add_right
-- for some reason mathport expected `Semiring` instead of `Distrib`?

