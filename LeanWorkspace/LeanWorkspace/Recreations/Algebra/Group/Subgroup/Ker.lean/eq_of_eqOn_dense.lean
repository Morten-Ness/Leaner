import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [Monoid M]

theorem eq_of_eqOn_dense {s : Set G} (hs : closure s = ⊤) {f g : G →* M} (h : s.EqOn f g) : f = g := MonoidHom.eq_of_eqOn_top <| hs ▸ MonoidHom.eqOn_closure h

