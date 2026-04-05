import Mathlib

theorem Quaternion.equivTuple_apply (R : Type*) [Zero R] [One R] [Neg R] (x : ℍ[R]) :
    Quaternion.equivTuple R x = ![x.re, x.imI, x.imJ, x.imK] := rfl

