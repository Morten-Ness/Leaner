import Mathlib

variable (R : Type u)

variable [LinearOrderedAddCommMonoidWithTop R]

theorem mul_eq_zero_iff {R : Type*} [AddCommMonoid R]
    {a b : Tropical (WithTop R)} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  simp [← Tropical.untrop_inj_iff, WithTop.add_eq_top]

