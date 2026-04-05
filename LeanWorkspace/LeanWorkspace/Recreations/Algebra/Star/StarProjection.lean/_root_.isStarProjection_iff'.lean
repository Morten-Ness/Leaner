import Mathlib

variable {R : Type*}

variable {p q : R}

theorem _root_.isStarProjection_iff' [Mul R] [Star R] :
    IsStarProjection p ↔ p * p = p ∧ star p = p := isStarProjection_iff _

