import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem mem_toNonUnitalSubsemiring {S : Subsemiring R} {x : R} :
    x ∈ S.toNonUnitalSubsemiring ↔ x ∈ S := .rfl

