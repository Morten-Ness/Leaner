import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem im_smul [SMulZeroClass S R] (s : S) : (s • a).im = s • a.im := QuaternionAlgebra.im_smul a s

