import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem algebraMap_def : ⇑(algebraMap R ℍ[R]) = coe := rfl

