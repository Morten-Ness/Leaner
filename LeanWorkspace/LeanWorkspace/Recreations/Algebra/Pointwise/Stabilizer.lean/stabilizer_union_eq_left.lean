import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

theorem stabilizer_union_eq_left (hdisj : Disjoint s t) (hstab : stabilizer G s ≤ stabilizer G t)
    (hstab_union : stabilizer G (s ∪ t) ≤ stabilizer G t) :
    stabilizer G (s ∪ t) = stabilizer G s := by
  refine le_antisymm ?_ ?_
  · calc
      stabilizer G (s ∪ t)
        ≤ stabilizer G (s ∪ t) ⊓ stabilizer G t := by simpa
      _ ≤ stabilizer G ((s ∪ t) \ t) := MulAction.stabilizer_inf_stabilizer_le_stabilizer_sdiff
      _ = stabilizer G s := by rw [union_diff_cancel_right]; simpa [← disjoint_iff_inter_eq_empty]
  · calc
      stabilizer G s
        ≤ stabilizer G s ⊓ stabilizer G t := by simpa
      _ ≤ stabilizer G (s ∪ t) := MulAction.stabilizer_inf_stabilizer_le_stabilizer_union

