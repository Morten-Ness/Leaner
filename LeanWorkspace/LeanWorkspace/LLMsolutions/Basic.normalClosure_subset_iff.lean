import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalClosure_subset_iff {N : Subgroup G} [N.Normal] : s ⊆ N ↔ Subgroup.normalClosure s ≤ N := by
  constructor
  · intro hs
    rw [Subgroup.normalClosure_eq_iInf]
    intro x hx
    simp only [Subgroup.mem_iInf] at hx ⊢
    exact hx N ‹N.Normal› hs
  · intro h
    intro x hx
    exact h (Subgroup.subset_normalClosure hx)
