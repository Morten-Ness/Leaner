import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_pos_iff [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftStrictMono R] [AddLeftReflectLT R] :
    0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := ⟨pos_and_pos_or_neg_and_neg_of_mul_pos, fun h =>
    h.elim (and_imp.2 mul_pos) (and_imp.2 mul_pos_of_neg_of_neg)⟩

