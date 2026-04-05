import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem mem_sup_of_normal_left {s t : Subgroup G} [hs : s.Normal] {x : G} :
    x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  have h := (sup_comm t s) ▸ Subgroup.mem_sup_of_normal_right (s := t) (t := s) (x := x)
  exact h.trans
    ⟨fun ⟨y, hy, z, hz, hp⟩ ↦ ⟨y * z * y⁻¹, hs.conj_mem z hz y, y, hy, by simp [hp]⟩,
    fun ⟨y, hy, z, hz, hp⟩ ↦ ⟨z, hz, z⁻¹ * y * z, hs.conj_mem' y hy z, by simp [mul_assoc, hp]⟩⟩

