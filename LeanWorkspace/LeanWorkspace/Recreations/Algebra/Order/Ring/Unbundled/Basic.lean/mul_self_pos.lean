import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftStrictMono R] [AddLeftReflectLT R]
    {a : R} : 0 < a * a ↔ a ≠ 0 := by
  constructor
  · rintro h rfl
    rw [mul_zero] at h
    exact h.false
  · intro h
    rcases h.lt_or_gt with h | h
    exacts [mul_pos_of_neg_of_neg h h, mul_pos h h]

