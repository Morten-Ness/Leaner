import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H := inv_mem

