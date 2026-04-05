import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem comap_ker {P : Type*} [MulOneClass P] (g : N →* P) (f : G →* N) :
    g.ker.comap f = (g.comp f).ker := rfl

