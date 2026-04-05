import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

theorem mul_le_mul_of_nonneg_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hbd : b ≤ d) (hc : 0 ≤ c) (hb : b ≤ 0) : a * b ≤ c * d := (mul_le_mul_of_nonpos_right hca hb).trans <| by gcongr; assumption

