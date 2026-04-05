import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_prodMap {G' : Type*} {N' : Type*} [Group G'] [Group N'] (f : G →* N) (g : G' →* N') :
    (prodMap f g).ker = f.ker.prod g.ker := by
  rw [← comap_bot, ← comap_bot, ← comap_bot, ← MonoidHom.prodMap_comap_prod, Subgroup.bot_prod_bot]

