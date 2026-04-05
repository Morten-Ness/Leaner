import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

theorem mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : b ≤ a) (hc : c ≤ 0) : c * a ≤ c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := d * b + d * a) ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
    _ ≤ d * a := by gcongr; exact hcd.trans_le <| add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

