FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem map_eq_map_iff {f : G →* N} {H K : Subgroup G} :
    H.map f = K.map f ↔ H ⊔ f.ker = K ⊔ f.ker := by
  constructor
  · intro h
    simpa [h]
  · intro h
    exact Subgroup.map_eq_map_iff.2 h
