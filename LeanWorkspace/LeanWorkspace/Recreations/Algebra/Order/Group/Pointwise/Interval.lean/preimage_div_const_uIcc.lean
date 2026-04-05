import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_div_const_uIcc (ha : a ≠ 0) (b c : α) :
    (fun x => x / a) ⁻¹' [[b, c]] = [[b * a, c * a]] := by
  simp only [div_eq_mul_inv, Set.preimage_mul_const_uIcc (inv_ne_zero ha), inv_inv]

