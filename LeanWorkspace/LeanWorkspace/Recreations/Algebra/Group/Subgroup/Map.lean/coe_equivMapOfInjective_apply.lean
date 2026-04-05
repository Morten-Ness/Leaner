import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (f : G →* N)

theorem coe_equivMapOfInjective_apply (H : Subgroup G) (f : G →* N) (hf : Function.Injective f)
    (h : H) : (Subgroup.equivMapOfInjective H f hf h : N) = f h := rfl

