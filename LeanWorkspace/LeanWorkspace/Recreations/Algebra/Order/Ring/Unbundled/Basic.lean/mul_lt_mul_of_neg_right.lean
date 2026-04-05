import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

theorem mul_lt_mul_of_neg_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (h : b < a) (hc : c < 0) : a * c < b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (b * d + a * d)).1 ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
    _ < a * d := mul_lt_mul_of_pos_right h <| hcd.trans_lt <| add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

