import Mathlib

variable {S M G : Type*}

variable [Semigroup S] {a b x y z x' y' : S}

theorem mul_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x * x') (y * y') := by
  exact h.mul_right h'
