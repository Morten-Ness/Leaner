import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem conj_mem_conjugatesOfSet {x c : G} :
    x ∈ Group.conjugatesOfSet s → c * x * c⁻¹ ∈ Group.conjugatesOfSet s := fun H => by
  rcases Group.mem_conjugatesOfSet_iff.1 H with ⟨a, h₁, h₂⟩
  exact Group.mem_conjugatesOfSet_iff.2 ⟨a, h₁, h₂.trans (isConj_iff.2 ⟨c, rfl⟩)⟩

