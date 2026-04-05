import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

theorem stabilizer_union_eq_right (hdisj : Disjoint s t) (hstab : stabilizer G t ≤ stabilizer G s)
    (hstab_union : stabilizer G (s ∪ t) ≤ stabilizer G s) :
    stabilizer G (s ∪ t) = stabilizer G t := by
  rw [union_comm, MulAction.stabilizer_union_eq_left hdisj.symm hstab (union_comm .. ▸ hstab_union)]

