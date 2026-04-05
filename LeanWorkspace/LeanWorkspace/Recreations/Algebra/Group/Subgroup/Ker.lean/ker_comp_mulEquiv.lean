import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_comp_mulEquiv {P : Type*} [MulOneClass P] (g : N →* P) (iso : G ≃* N) :
    (g.comp iso).ker = map (iso.symm : N →* G) g.ker := by
  rw [← MonoidHom.comap_ker, comap_equiv_eq_map_symm]

