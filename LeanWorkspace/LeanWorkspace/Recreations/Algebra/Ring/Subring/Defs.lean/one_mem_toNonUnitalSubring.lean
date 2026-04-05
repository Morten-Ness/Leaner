import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

theorem one_mem_toNonUnitalSubring (S : Subring R) : 1 ∈ S.toNonUnitalSubring := S.one_mem

