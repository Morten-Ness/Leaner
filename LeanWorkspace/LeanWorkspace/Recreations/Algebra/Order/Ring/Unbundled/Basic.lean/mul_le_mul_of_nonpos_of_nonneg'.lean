import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

theorem mul_le_mul_of_nonpos_of_nonneg' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : d ≤ 0) : a * b ≤ c * d := (mul_le_mul_of_nonneg_left hbd ha).trans <| mul_le_mul_of_nonpos_right hca hd

