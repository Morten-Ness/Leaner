import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem re_smul [SMul S R] (s : S) : (s • a).re = s • a.re := rfl

