FAIL
import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem mem_sup_of_normal_left {s t : Subgroup G} [hs : s.Normal] {x : G} :
    x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  constructor
  · intro hx
    rw [Subgroup.mem_sup] at hx
    rcases hx with ⟨y, hy, z, hz, rfl⟩
    refine ⟨y, hy, z, hz, rfl⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    rw [Subgroup.mem_sup]
    exact ⟨y, hy, z, hz, rfl⟩
