import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [Monoid M]

theorem eq_of_eqOn_top {f g : G →* M} (h : Set.EqOn f g (⊤ : Subgroup G)) : f = g := ext fun _x => h trivial

