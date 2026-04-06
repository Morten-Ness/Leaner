import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem coe_eq_singleton {H : Subgroup G} : (∃ g : G, (H : Set G) = {g}) ↔ H = ⊥ := by
  constructor
  · rintro ⟨g, hg⟩
    have h1 : (1 : G) = g := by
      have : (1 : G) ∈ (H : Set G) := H.one_mem
      rw [hg] at this
      simpa using this
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ ({g} : Set G) := by
        rw [← hg]
        exact hx
      have hxg : x = g := by simpa using hx'
      rw [Subgroup.mem_bot]
      simpa [h1] using hxg
    · intro x hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      exact H.one_mem
  · intro h
    refine ⟨1, ?_⟩
    rw [h]
    ext x
    simp
