import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_bot {x : G} : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Iff.rfl

