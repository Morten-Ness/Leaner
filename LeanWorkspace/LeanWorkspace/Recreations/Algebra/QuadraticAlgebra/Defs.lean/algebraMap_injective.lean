import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [CommSemiring R]

theorem algebraMap_injective : (algebraMap R (QuadraticAlgebra R a b) : _ → _).Injective := fun _ _ ↦ by simp [QuadraticAlgebra.algebraMap_eq]

