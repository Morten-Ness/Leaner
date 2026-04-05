import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_equiv_eq_comap_symm (f : G ≃* N) (K : Subgroup G) :
    K.map f = K.comap (G := N) f.symm :=
  Subgroup.map_equiv_eq_comap_symm' _ _

