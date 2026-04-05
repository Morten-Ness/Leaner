import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_nonneg_iff [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] :
    0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg, fun h =>
    h.elim (and_imp.2 mul_nonneg) (and_imp.2 mul_nonneg_of_nonpos_of_nonpos)⟩

