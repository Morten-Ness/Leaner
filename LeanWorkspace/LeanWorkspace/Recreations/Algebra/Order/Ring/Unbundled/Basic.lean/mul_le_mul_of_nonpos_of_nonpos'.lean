import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

theorem mul_le_mul_of_nonpos_of_nonpos' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hdb : d ≤ b) (ha : a ≤ 0) (hd : d ≤ 0) : a * b ≤ c * d := (mul_le_mul_of_nonpos_left hdb ha).trans <| mul_le_mul_of_nonpos_right hca hd

