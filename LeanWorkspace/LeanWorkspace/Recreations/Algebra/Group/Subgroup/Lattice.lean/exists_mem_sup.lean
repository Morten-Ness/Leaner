import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem exists_mem_sup :
    (∃ x ∈ s ⊔ t, P x) ↔ (∃ x₁ ∈ s, ∃ x₂ ∈ t, P (x₁ * x₂)) := by
  simp [Subgroup.mem_sup]

