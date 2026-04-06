FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_zsmul_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : ℤ) : f (n • a) = f 0 + n • b := by
  simpa only [sub_eq_add_neg, zsmul_eq_mul, Int.cast_id] using
    AddMonoidHom.map_intCast_zsmul
      ({ toFun := fun x => f x - f 0
         map_zero' := by simp
         map_add' := by
           intro x y
           rw [map_add_const, map_add_const]
           abel } : G →+ H) n a
