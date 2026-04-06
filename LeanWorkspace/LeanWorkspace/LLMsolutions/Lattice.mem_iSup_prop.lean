FAIL
import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem mem_iSup_prop {p : Prop} {K : p → Subgroup G} {x : G} :
    x ∈ ⨆ (h : p), K h ↔ x = 1 ∨ ∃ (h : p), x ∈ K h := by
  classical
  by_cases hp : Nonempty p
  · letI : Nonempty p := hp
    constructor
    · intro hx
      rw [Subgroup.mem_iSup_of_directed] at hx
      · simpa using hx
      · intro a b
        refine ⟨Classical.choice hp, ?_, ?_⟩ <;> simp
    · intro hx
      rw [Subgroup.mem_iSup_of_directed]
      · simpa using hx
      · intro a b
        refine ⟨Classical.choice hp, ?_, ?_⟩ <;> simp
  · have hp' : IsEmpty p := not_nonempty_iff.mp hp
    letI : IsEmpty p := hp'
    rw [iSup_of_empty, Subgroup.mem_bot]
    constructor
    · intro hx
      exact Or.inl hx
    · intro hx
      rcases hx with rfl | h
      · rfl
      · rcases h with ⟨h, _⟩
        exact (hp ⟨h⟩).elim
