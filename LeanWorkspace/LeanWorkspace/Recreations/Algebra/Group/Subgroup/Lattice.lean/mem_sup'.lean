import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

theorem mem_sup' : x ∈ s ⊔ t ↔ ∃ (y : s) (z : t), (y : C) * z = x := Subgroup.mem_sup.trans <| by simp only [SetLike.exists, exists_prop]

