import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem toSubring_injective {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] :
    Function.Injective (Subalgebra.toSubring : Subalgebra R A → Subring A) := fun S T h =>
  Subalgebra.ext fun x => by rw [← Subalgebra.mem_toSubring, ← Subalgebra.mem_toSubring, h]

