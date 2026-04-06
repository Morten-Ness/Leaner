import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_equiv_eq_comap_symm (f : G ≃* N) (K : Subgroup G) :
    K.map f.toMonoidHom = K.comap f.symm.toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    refine ⟨f.symm x, hx, ?_⟩
    simp
