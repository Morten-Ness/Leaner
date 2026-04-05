import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem prod_mono_left (H : Subgroup N) : Monotone fun K : Subgroup G => K.prod H := fun _ _ hs =>
  Subgroup.prod_mono hs (le_refl H)

