import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [Zero R]

theorem C_inj {x y : R} : (.C x : QuadraticAlgebra R a b) = .C y ↔ x = y := QuadraticAlgebra.C_injective.eq_iff

