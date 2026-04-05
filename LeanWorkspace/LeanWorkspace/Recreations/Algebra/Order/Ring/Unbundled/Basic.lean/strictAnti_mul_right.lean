import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

variable [Preorder α] {f : α → R}

theorem strictAnti_mul_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a : R} (ha : a < 0) : StrictAnti fun x => x * a := fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_right b_lt_c ha

