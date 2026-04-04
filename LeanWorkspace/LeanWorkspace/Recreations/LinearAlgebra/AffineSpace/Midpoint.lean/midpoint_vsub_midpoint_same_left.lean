import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

variable (R)

theorem midpoint_vsub_midpoint_same_left (p₁ p₂ p₃ : P) :
    midpoint R p₁ p₂ -ᵥ midpoint R p₁ p₃ = (⅟2 : R) • (p₂ -ᵥ p₃) := by
  rw [midpoint_vsub_midpoint, vsub_self, midpoint_eq_smul_add, zero_add]

