import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_inf_eq (H K : Subgroup G) (f : G →* N) (hf : Function.Injective f) :
    Subgroup.map f (H ⊓ K) = Subgroup.map f H ⊓ Subgroup.map f K := by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

