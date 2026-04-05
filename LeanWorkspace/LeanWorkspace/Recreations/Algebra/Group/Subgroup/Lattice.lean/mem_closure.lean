import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem mem_closure {x : G} : x ∈ Subgroup.closure k ↔ ∀ K : Subgroup G, k ⊆ K → x ∈ K := Subgroup.mem_sInf

