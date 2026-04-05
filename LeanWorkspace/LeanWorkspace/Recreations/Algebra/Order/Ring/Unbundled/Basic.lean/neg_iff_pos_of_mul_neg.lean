import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem neg_iff_pos_of_mul_neg [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hab : a * b < 0) : a < 0 ↔ 0 < b := ⟨pos_of_mul_neg_right hab ∘ le_of_lt, neg_of_mul_neg_left hab ∘ le_of_lt⟩

