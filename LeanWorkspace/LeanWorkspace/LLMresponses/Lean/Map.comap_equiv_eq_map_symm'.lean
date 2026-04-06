import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem comap_equiv_eq_map_symm' (f : N ≃* G) (K : Subgroup G) :
    K.comap f.toMonoidHom = K.map f.symm.toMonoidHom := by
  ext x
  constructor
  · intro hx
    exact ⟨f x, hx, by simp⟩
  · rintro ⟨y, hy, hxy⟩
    rw [← hxy]
    simpa using hy
