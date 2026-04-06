import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem bot_or_exists_ne_one (H : Subgroup G) : H = ⊥ ∨ ∃ x ∈ H, x ≠ (1 : G) := by
  by_cases h : H = ⊥
  · exact Or.inl h
  · right
    by_contra h'
    apply h
    ext x
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · rw [Subgroup.mem_bot]
        exact hx1
      · exfalso
        apply h'
        exact ⟨x, hx, hx1⟩
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact H.one_mem
