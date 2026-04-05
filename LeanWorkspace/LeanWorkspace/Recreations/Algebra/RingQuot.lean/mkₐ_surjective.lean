import Mathlib

variable {R : Type uR} [Semiring R]

variable {S : Type uS} [CommSemiring S]

variable {T : Type uT}

variable {A : Type uA} [Semiring A] [Algebra S A]

theorem mkₐ_surjective (c : RingCon A) :
    Function.Surjective (c.mkₐ (S := S)) :=
  mk'_surjective c

