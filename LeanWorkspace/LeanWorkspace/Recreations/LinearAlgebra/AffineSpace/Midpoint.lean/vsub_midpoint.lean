import Mathlib

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

variable {R} {x y z : P}

theorem vsub_midpoint (p₁ p₂ p : P) :
    p -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p -ᵥ p₁) + (⅟2 : R) • (p -ᵥ p₂) := by
  rw [← neg_vsub_eq_vsub_rev, midpoint_vsub, neg_add, ← smul_neg, ← smul_neg, neg_vsub_eq_vsub_rev,
    neg_vsub_eq_vsub_rev]

