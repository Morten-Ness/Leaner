import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

theorem mul_lt_mul_of_neg_left [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (h : b < a) (hc : c < 0) : c * a < c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (d * b + d * a)).1 ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
    _ < d * a := mul_lt_mul_of_pos_left h <| hcd.trans_lt <| add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

