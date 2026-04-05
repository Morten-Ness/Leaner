import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

theorem mem_sup : x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := ⟨fun h => by
    rw [Subgroup.sup_eq_closure] at h
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ h
    · rintro y (h | h)
      · exact ⟨y, h, 1, t.one_mem, by simp⟩
      · exact ⟨1, s.one_mem, y, h, by simp⟩
    · exact ⟨1, s.one_mem, 1, ⟨t.one_mem, mul_one 1⟩⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      exact ⟨_, mul_mem hy₁ hy₂, _, mul_mem hz₁ hz₂, by simp [mul_assoc, mul_left_comm]⟩
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      exact ⟨_, inv_mem hy, _, inv_mem hz, mul_comm z y ▸ (mul_inv_rev z y).symm⟩, by
    rintro ⟨y, hy, z, hz, rfl⟩; exact Subgroup.mul_mem_sup hy hz⟩

