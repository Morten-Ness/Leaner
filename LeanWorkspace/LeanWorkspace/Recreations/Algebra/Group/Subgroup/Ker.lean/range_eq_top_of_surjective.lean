import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem range_eq_top_of_surjective {N} [Group N] (f : G →* N) (hf : Function.Surjective f) :
    f.range = (⊤ : Subgroup N) := MonoidHom.range_eq_top.2 hf

