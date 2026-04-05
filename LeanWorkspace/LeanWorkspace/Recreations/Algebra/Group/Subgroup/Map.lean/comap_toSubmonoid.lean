import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (f : G →* N)

theorem comap_toSubmonoid (e : G ≃* N) (s : Subgroup N) :
    (s.comap e).toSubmonoid = s.toSubmonoid.comap e.toMonoidHom := rfl

