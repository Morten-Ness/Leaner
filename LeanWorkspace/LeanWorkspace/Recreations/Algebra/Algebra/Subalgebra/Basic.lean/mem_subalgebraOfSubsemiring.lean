import Mathlib

variable {R : Type*} [Semiring R]

theorem mem_subalgebraOfSubsemiring {x : R} {S : Subsemiring R} :
    x ∈ subalgebraOfSubsemiring S ↔ x ∈ S := Iff.rfl

