import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

variable [Preorder α] {f g : α → R}

theorem antitone_mul_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a : R} (ha : a ≤ 0) : Antitone fun x => x * a := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_right b_le_c ha

