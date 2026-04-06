import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_equiv_top {F : Type*} [EquivLike F G N] [MulEquivClass F G N] (f : F) :
    Subgroup.map (f : G →* N) ⊤ = ⊤ := by
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    rcases EquivLike.surjective f x with ⟨y, rfl⟩
    exact ⟨y, trivial, rfl⟩
