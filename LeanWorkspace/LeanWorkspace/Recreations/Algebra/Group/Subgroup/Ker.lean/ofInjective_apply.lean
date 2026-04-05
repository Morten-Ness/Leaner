import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem ofInjective_apply {f : G →* N} (hf : Function.Injective f) {x : G} :
    ↑(MonoidHom.ofInjective hf x) = f x := rfl

