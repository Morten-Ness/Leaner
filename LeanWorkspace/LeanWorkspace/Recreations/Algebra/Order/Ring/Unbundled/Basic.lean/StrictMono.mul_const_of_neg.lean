import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

variable [Preorder α] {f : α → R}

theorem StrictMono.mul_const_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictMono f) (ha : a < 0) : StrictAnti fun x => f x * a := (strictAnti_mul_right ha).comp_strictMono hf

