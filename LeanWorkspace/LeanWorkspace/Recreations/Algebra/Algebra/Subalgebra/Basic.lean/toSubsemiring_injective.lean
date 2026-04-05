import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : Subalgebra R A → Subsemiring A) := fun S T h =>
  Subalgebra.ext fun x => by rw [← Subalgebra.mem_toSubsemiring, ← Subalgebra.mem_toSubsemiring, h]

