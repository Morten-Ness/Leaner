import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_nsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℕ) : f (x - n • a) = f x - n • b := by
  conv_rhs => rw [← sub_add_cancel x (n • a), AddConstMapClass.map_add_nsmul, add_sub_cancel_right]

