import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

theorem mul_le_mul_of_nonpos_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hdb : d ≤ b) (hc : c ≤ 0) (hb : b ≤ 0) : a * b ≤ c * d := (mul_le_mul_of_nonpos_right hca hb).trans <| mul_le_mul_of_nonpos_left hdb hc

