import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [Zero R]

theorem C_injective : Function.Injective (.C : R → QuadraticAlgebra R a b) := fun _ _ h => congr_arg re h

