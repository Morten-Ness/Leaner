import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem comap_equiv_eq_map_symm (f : N ≃* G) (K : Subgroup G) :
    Subgroup.comap (f : N →* G) K = K.map (f.symm : G →* N) := by
  ext x
  constructor
  · intro hx
    refine ⟨f x, hx, ?_⟩
    simp
  · rintro ⟨y, hy, hxy⟩
    rw [← hxy]
    simpa using hy
