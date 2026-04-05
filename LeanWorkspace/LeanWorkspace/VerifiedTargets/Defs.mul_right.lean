import Mathlib

variable {S M G : Type*}

variable [Semigroup S] {a b x y z x' y' : S}

theorem mul_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x * x') (y * y') := by
  unfold SemiconjBy
  -- TODO this could be done using `assoc_rw` if/when this is ported to mathlib4
  rw [← mul_assoc, SemiconjBy.eq h, mul_assoc, SemiconjBy.eq h', ← mul_assoc]

