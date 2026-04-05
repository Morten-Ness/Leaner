import Mathlib

variable {α β M N : Type*}

variable {G : Type*} [Group G] {s t : Set α}

theorem mulIndicator_diff (h : s ⊆ t) (f : α → G) :
    mulIndicator (t \ s) f = mulIndicator t f * (mulIndicator s f)⁻¹ := eq_mul_inv_of_mul_eq <| by
    rw [Pi.mul_def, ← Set.mulIndicator_union_of_disjoint, diff_union_self,
      union_eq_self_of_subset_right h]
    exact disjoint_sdiff_self_left

