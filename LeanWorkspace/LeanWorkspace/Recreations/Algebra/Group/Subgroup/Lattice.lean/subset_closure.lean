import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem subset_closure : k ⊆ Subgroup.closure k := fun _ hx => Subgroup.mem_closure.2 fun _ hK => hK hx

