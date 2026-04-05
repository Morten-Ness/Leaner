import Mathlib

variable {R : Type*}

variable [Field R] (a b : ℍ[R])

variable [LinearOrder R] [IsStrictOrderedRing R] (a b : ℍ[R])

theorem coe_div (x y : R) : ((x / y : R) : ℍ[R]) = x / y := map_div₀ (algebraMap R ℍ[R]) x y

