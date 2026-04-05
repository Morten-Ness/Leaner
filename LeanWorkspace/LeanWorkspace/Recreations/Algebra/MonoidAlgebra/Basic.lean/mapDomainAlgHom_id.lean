import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem mapDomainAlgHom_id : MonoidAlgebra.mapDomainAlgHom R A (.id M) = .id R A[M] := by
  ext; simp [MonoidHom.id, ← Function.id_def]

