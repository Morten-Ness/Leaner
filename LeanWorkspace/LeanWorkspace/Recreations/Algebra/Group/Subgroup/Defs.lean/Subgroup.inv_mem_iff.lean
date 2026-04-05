import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem inv_mem_iff {x : G} : x⁻¹ ∈ H ↔ x ∈ H := inv_mem_iff

