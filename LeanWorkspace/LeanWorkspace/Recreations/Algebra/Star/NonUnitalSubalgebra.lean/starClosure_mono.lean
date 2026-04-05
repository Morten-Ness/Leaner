import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [StarModule R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem starClosure_mono : Monotone (NonUnitalSubalgebra.starClosure (R := R) (A := A)) :=
  fun _ _ h => NonUnitalSubalgebra.starClosure_le <| h.trans le_sup_left

