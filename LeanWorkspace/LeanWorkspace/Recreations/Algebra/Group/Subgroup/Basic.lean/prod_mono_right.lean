import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem prod_mono_right (K : Subgroup G) : Monotone fun t : Subgroup N => K.prod t := Subgroup.prod_mono (le_refl K)

