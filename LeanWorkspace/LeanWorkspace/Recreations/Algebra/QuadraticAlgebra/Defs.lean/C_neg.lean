import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

theorem C_neg [NegZeroClass R] (x : R) : (.C (-x) : QuadraticAlgebra R a b) = -.C x := by
  ext <;> simp

