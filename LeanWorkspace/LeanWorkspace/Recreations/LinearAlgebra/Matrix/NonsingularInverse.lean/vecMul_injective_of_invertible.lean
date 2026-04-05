import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [DecidableEq m] {R K : Type*} [CommRing R] [Field K] [Fintype m]

theorem vecMul_injective_of_invertible (A : Matrix m m K) [Invertible A] :
    Function.Injective A.vecMul := Matrix.vecMul_injective_iff_isUnit.2 <| isUnit_of_invertible A

