import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem one_mem_toNonUnitalSubsemiring (S : Subsemiring R) : (1 : R) ∈ S.toNonUnitalSubsemiring := S.one_mem

