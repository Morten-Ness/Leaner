import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem mem_map_equiv {f : G ≃* N} {K : Subgroup G} {x : N} :
    x ∈ K.map f.toMonoidHom ↔ f.symm x ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    refine ⟨f.symm x, hx, ?_⟩
    exact f.apply_symm_apply x
