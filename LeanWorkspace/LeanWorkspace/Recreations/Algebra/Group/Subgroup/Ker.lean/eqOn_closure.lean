import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

variable {M : Type*} [Monoid M]

theorem eqOn_closure {f g : G →* M} {s : Set G} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) := show closure s ≤ f.eqLocus g from (closure_le _).2 h

