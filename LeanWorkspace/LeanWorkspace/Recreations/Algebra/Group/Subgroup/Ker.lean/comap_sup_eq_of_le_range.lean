import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem comap_sup_eq_of_le_range {H K : Subgroup N} (hH : H ≤ f.range) (hK : K ≤ f.range) :
    comap f H ⊔ comap f K = comap f (H ⊔ K) := Subgroup.map_injective_of_ker_le f ((Subgroup.ker_le_comap f H).trans le_sup_left) (Subgroup.ker_le_comap f (H ⊔ K))
    (by
      rw [Subgroup.map_comap_eq, map_sup, Subgroup.map_comap_eq, Subgroup.map_comap_eq, inf_eq_right.mpr hH,
        inf_eq_right.mpr hK, inf_eq_right.mpr (sup_le hH hK)])

