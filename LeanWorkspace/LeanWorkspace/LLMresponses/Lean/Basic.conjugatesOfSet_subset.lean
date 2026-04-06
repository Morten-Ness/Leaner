FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem conjugatesOfSet_subset {s : Set G} {N : Subgroup G} [N.Normal] (h : s ⊆ N) :
    Group.conjugatesOfSet s ⊆ N := by
  intro x hx
  rw [Group.mem_conjugatesOfSet_iff] at hx
  rcases hx with ⟨y, hy, g, rfl⟩
  exact N.conj_mem g (h hy)
