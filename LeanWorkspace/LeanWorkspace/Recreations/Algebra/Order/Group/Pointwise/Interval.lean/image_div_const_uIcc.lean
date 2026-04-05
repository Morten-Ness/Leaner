import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem image_div_const_uIcc (a b c : α) : (fun x => x / a) '' [[b, c]] = [[b / a, c / a]] := by
  simp only [div_eq_mul_inv, Set.image_mul_const_uIcc]

