import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

variable (f : G →* N)

theorem subgroupOf_sup {A A' B : Subgroup G} (hA : A ≤ B) (hA' : A' ≤ B) :
    (A ⊔ A').subgroupOf B = A.subgroupOf B ⊔ A'.subgroupOf B := by
  refine
    Subgroup.map_injective_of_ker_le B.subtype (Subgroup.ker_le_comap _ _)
      (le_trans (Subgroup.ker_le_comap B.subtype _) le_sup_left) ?_
  simp only [subgroupOf, Subgroup.map_comap_eq, map_sup, range_subtype]
  rw [inf_of_le_right (sup_le hA hA'), inf_of_le_right hA', inf_of_le_right hA]

