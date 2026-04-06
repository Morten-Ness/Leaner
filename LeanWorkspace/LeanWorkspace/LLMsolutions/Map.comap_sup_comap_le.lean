import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem comap_sup_comap_le (H K : Subgroup N) (f : G →* N) :
    Subgroup.comap f H ⊔ Subgroup.comap f K ≤ Subgroup.comap f (H ⊔ K) := by
  rw [sup_le_iff]
  constructor
  · exact Subgroup.comap_mono le_sup_left
  · exact Subgroup.comap_mono le_sup_right
