import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem mem_sup_of_normal_right {s t : Subgroup G} [ht : t.Normal] {x : G} :
    x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  constructor
  · intro hx; rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro x (hx | hx)
      · exact ⟨x, hx, 1, t.one_mem, by simp⟩
      · exact ⟨1, s.one_mem, x, hx, by simp⟩
    · exact ⟨1, s.one_mem, 1, t.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      exact ⟨y₁ * y₂, s.mul_mem hy₁ hy₂,
            (y₂⁻¹ * z₁ * y₂) * z₂, t.mul_mem (ht.conj_mem' z₁ hz₁ y₂) hz₂, by simp [mul_assoc]⟩
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      exact ⟨y⁻¹, s.inv_mem hy,
            y * z⁻¹ * y⁻¹, ht.conj_mem z⁻¹ (t.inv_mem hz) y, by simp [mul_assoc]⟩
  · rintro ⟨y, hy, z, hz, rfl⟩; exact Subgroup.mul_mem_sup hy hz

