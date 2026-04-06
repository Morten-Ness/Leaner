import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem eq_bot_of_subsingleton [Subsingleton H] : H = ⊥ := by
  ext x
  constructor
  · intro hx
    have hx1 : (⟨x, hx⟩ : H) = 1 := Subsingleton.elim _ _
    change x = 1
    exact Subtype.ext_iff.mp hx1
  · intro hx
    rw [Subgroup.mem_bot] at hx
    simp [hx]
