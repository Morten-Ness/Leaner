import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [Zero R]

variable [One R]

theorem C_eq_one_iff {r : R} : (.C r : QuadraticAlgebra R a b) = 1 ↔ r = 1 := by
  rw [← QuadraticAlgebra.C_one, QuadraticAlgebra.C_inj]

