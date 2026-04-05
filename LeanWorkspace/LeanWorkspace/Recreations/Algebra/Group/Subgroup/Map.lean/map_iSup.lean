import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_iSup {ι : Sort*} (f : G →* N) (s : ι → Subgroup G) :
    (iSup s).map f = ⨆ i, (s i).map f := (Subgroup.gc_map_comap f).l_iSup

