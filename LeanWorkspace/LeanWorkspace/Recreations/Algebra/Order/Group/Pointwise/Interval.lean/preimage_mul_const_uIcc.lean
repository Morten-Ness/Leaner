import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_mul_const_uIcc (ha : a ≠ 0) (b c : α) :
    (· * a) ⁻¹' [[b, c]] = [[b / a, c / a]] := (lt_or_gt_of_ne ha).elim
    (fun h => by
      simp [← Icc_min_max, h, h.le, min_div_div_right_of_nonpos, max_div_div_right_of_nonpos])
    fun ha : 0 < a => by simp [← Icc_min_max, ha, ha.le, min_div_div_right, max_div_div_right]

