import Mathlib

open scoped Int Relator

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem prod_mono : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) (@Subgroup.prod G _ N _) (@Subgroup.prod G _ N _) := fun _s _s' hs _t _t' ht => Set.prod_mono hs ht

