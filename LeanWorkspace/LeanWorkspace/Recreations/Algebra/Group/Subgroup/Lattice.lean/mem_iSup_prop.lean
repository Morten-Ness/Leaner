import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem mem_iSup_prop {p : Prop} {K : p → Subgroup G} {x : G} :
    x ∈ ⨆ (h : p), K h ↔ x = 1 ∨ ∃ (h : p), x ∈ K h := by
  by_cases h : p <;>
  simp +contextual [h]

