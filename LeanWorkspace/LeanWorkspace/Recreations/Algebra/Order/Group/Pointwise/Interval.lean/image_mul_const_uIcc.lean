import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem image_mul_const_uIcc (a b c : α) : (· * a) '' [[b, c]] = [[b * a, c * a]] := if ha : a = 0 then by simp [ha]
  else calc
    (fun x => x * a) '' [[b, c]] = (· * a⁻¹) ⁻¹' [[b, c]] :=
      (Units.mk0 a ha).mulRight.image_eq_preimage_symm _
    _ = (fun x => x / a) ⁻¹' [[b, c]] := by simp only [div_eq_mul_inv]
    _ = [[b * a, c * a]] := Set.preimage_div_const_uIcc ha _ _

