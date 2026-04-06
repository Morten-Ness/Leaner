import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem toSubring_injective {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] :
    Function.Injective (Subalgebra.toSubring : Subalgebra R A → Subring A) := by
  intro S T h
  ext x
  change x ∈ (S.toSubring : Subring A) ↔ x ∈ (T.toSubring : Subring A)
  simpa [h]
