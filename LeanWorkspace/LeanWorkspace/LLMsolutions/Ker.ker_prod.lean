import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [MulOneClass M]

theorem ker_prod {M N : Type*} [MulOneClass M] [MulOneClass N] (f : G →* M) (g : G →* N) :
    (f.prod g).ker = f.ker ⊓ g.ker := by
  ext x
  simp [MonoidHom.mem_ker]
