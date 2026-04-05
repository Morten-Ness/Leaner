import Mathlib

variable {S M G : Type*}

variable [Semigroup S] {a b x y z x' y' : S}

theorem mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b x y) : SemiconjBy (a * b) x z := by
  unfold SemiconjBy
  rw [mul_assoc, SemiconjBy.eq hb, ← mul_assoc, SemiconjBy.eq ha, mul_assoc]

