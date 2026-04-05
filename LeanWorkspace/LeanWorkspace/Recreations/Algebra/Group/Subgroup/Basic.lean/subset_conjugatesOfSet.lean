import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem subset_conjugatesOfSet : s ⊆ Group.conjugatesOfSet s := fun (x : G) (h : x ∈ s) =>
  Group.mem_conjugatesOfSet_iff.2 ⟨x, h, IsConj.refl _⟩

