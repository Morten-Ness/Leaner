import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem star_mem_iff {U : R} : star U ∈ unitary R ↔ U ∈ unitary R := ⟨fun h => star_star U ▸ Unitary.star_mem h, Unitary.star_mem⟩

