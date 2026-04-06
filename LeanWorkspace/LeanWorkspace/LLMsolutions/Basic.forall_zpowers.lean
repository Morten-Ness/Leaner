import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem forall_zpowers {x : G} {p : Subgroup.zpowers x → Prop} : (∀ g, p g) ↔ ∀ m : ℤ, p ⟨x ^ m, m, rfl⟩ := by
  constructor
  · intro h m
    exact h ⟨x ^ m, m, rfl⟩
  · intro h g
    rcases g with ⟨g, m, rfl⟩
    exact h m
