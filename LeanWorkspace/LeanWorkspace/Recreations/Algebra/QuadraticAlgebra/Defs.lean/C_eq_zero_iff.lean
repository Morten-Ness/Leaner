import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [Zero R]

theorem C_eq_zero_iff {r : R} : (.C r : QuadraticAlgebra R a b) = 0 ↔ r = 0 := by
  rw [← QuadraticAlgebra.C_zero, QuadraticAlgebra.C_inj]

