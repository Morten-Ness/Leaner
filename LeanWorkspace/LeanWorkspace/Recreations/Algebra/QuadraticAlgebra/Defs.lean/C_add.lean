import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [AddZeroClass R]

theorem C_add (x y : R) : (.C (x + y) : QuadraticAlgebra R a b) = .C x + .C y := by
  ext <;> simp

