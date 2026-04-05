import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem coe_eq_one {x : S} : (x : A) = 1 ↔ x = 1 := by
  constructor
  · intro hx
    ext
    simpa using hx
  · intro hx
    simpa [hx]
