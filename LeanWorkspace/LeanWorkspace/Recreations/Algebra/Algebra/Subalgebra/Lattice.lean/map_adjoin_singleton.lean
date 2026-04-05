import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem map_adjoin_singleton (e : A →ₐ[R] B) (x : A) :
    (R[x]).map e = R[e x] := by
  rw [AlgHom.map_adjoin, Set.image_singleton]

