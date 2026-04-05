import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem algebraMap_injective : (algebraMap R ℍ[R] : _ → _).Injective := QuaternionAlgebra.algebraMap_injective

