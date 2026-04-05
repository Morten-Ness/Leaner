import Mathlib

variable {R : Type u} {α : Type*}

variable [Ring R] [LinearOrder R] {a b : R}

theorem mul_self_le_mul_self_of_le_of_neg_le
    [MulPosMono R] [PosMulMono R] [AddLeftMono R]
    (h₁ : a ≤ b) (h₂ : -a ≤ b) : a * a ≤ b * b := (le_total 0 a).elim (mul_self_le_mul_self · h₁) fun h ↦
    (neg_mul_neg a a).symm.trans_le <|
      mul_le_mul h₂ h₂ (neg_nonneg.2 h) <| (neg_nonneg.2 h).trans h₂

