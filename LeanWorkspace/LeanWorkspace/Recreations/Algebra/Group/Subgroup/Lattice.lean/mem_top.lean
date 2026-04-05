import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_top (x : G) : x ∈ (⊤ : Subgroup G) := Set.mem_univ x

