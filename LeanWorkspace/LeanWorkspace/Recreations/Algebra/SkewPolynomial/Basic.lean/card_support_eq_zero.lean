import Mathlib

variable {R : Type*}

variable [Semiring R] {p q : SkewPolynomial R}

variable {S S₁ S₂ : Type*}

set_option backward.isDefEq.respectTransparency false in
theorem card_support_eq_zero : p.support.card = 0 ↔ p = 0 := by simp

