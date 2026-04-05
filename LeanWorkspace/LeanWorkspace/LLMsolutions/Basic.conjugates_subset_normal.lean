FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem conjugates_subset_normal {N : Subgroup G} [tn : N.Normal] {a : G} (h : a ∈ N) :
    conjugatesOf a ⊆ N := by
  intro x hx
  rw [mem_conjugatesOf_iff] at hx
  rcases hx with ⟨g, rfl⟩
  exact Subgroup.Normal.conj_mem tn g h
