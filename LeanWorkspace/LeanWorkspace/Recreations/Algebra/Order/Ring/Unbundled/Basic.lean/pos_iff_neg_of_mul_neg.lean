import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem pos_iff_neg_of_mul_neg [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hab : a * b < 0) : 0 < a ↔ b < 0 := ⟨neg_of_mul_neg_right hab ∘ le_of_lt, pos_of_mul_neg_left hab ∘ le_of_lt⟩

