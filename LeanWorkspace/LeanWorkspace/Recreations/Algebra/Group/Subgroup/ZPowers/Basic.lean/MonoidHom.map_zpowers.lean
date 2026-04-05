import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem MonoidHom.map_zpowers (f : G →* N) (x : G) :
    (Subgroup.zpowers x).map f = Subgroup.zpowers (f x) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, f.map_closure, Set.image_singleton]

