import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem _root_.AddSubgroup.toSubgroup_comap {A A₂ : Type*} [AddGroup A] [AddGroup A₂]
    (f : A →+ A₂) (s : AddSubgroup A₂) :
    s.toSubgroup.comap (AddMonoidHom.toMultiplicative f) = AddSubgroup.toSubgroup (s.comap f) := rfl

