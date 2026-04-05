import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalClosure_le_normal {N : Subgroup G} [N.Normal] (h : s ⊆ N) : Subgroup.normalClosure s ≤ N := by
  intro a w
  refine closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_) (fun x _ ihx => ?_) w
  · exact Group.conjugatesOfSet_subset h hx
  · exact one_mem _
  · exact mul_mem ihx ihy
  · exact inv_mem ihx

