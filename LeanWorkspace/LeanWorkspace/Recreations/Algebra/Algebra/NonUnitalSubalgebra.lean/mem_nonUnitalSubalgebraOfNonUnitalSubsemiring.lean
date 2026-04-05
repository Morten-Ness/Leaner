import Mathlib

variable {R : Type*} [NonUnitalNonAssocSemiring R]

theorem mem_nonUnitalSubalgebraOfNonUnitalSubsemiring {x : R} {S : NonUnitalSubsemiring R} :
    x ∈ nonUnitalSubalgebraOfNonUnitalSubsemiring S ↔ x ∈ S := Iff.rfl

