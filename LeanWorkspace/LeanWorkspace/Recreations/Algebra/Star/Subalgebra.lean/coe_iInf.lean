import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem coe_iInf {ι : Sort*} {S : ι → StarSubalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
  simp [iInf]

