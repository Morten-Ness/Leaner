import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

theorem mul_le_mul_of_nonpos_of_nonneg [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hac : a ≤ c) (hdb : d ≤ b) (hc : c ≤ 0) (hb : 0 ≤ b) : a * b ≤ c * d := (mul_le_mul_of_nonneg_right hac hb).trans <| mul_le_mul_of_nonpos_left hdb hc

