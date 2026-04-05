import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

theorem mul_le_mul_of_nonpos_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := b * d + a * d) ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
    _ ≤ a * d := by gcongr; exact hcd.trans_le <| add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

