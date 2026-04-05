import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem ofLeftInverse_symm_apply {f : G →* N} {g : N →* G} (h : Function.LeftInverse g f)
    (x : f.range) : (MonoidHom.ofLeftInverse h).symm x = g x := rfl

