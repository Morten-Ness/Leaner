import Mathlib

variable {R : Type*} [Ring R]

variable {S : Type*} [Semiring S]

theorem mem_subalgebraOfSubring {x : R} {S : Subring R} : x ∈ subalgebraOfSubring S ↔ x ∈ S := Iff.rfl

