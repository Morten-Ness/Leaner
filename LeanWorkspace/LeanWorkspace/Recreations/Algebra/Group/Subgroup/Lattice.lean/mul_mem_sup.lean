import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mul_mem_sup {S T : Subgroup G} {x y : G} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T := (S ⊔ T).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)

