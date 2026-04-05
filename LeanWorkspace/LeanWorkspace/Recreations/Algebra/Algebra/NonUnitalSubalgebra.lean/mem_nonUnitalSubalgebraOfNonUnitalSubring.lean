import Mathlib

variable {R : Type*} [NonUnitalNonAssocRing R]

theorem mem_nonUnitalSubalgebraOfNonUnitalSubring {x : R} {S : NonUnitalSubring R} :
    x ∈ nonUnitalSubalgebraOfNonUnitalSubring S ↔ x ∈ S := Iff.rfl

