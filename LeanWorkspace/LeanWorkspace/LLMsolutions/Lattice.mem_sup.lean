import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

theorem mem_sup : x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  constructor
  · intro hx
    rw [Subgroup.mem_sup] at hx
    rcases hx with ⟨y, hy, z, hz, rfl⟩
    exact ⟨y, hy, z, hz, rfl⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    rw [Subgroup.mem_sup]
    exact ⟨y, hy, z, hz, rfl⟩
