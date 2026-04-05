import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommRing R]

variable [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B] [NonUnitalNonAssocRing C]

variable [Module R A] [Module R B] [Module R C]

theorem toNonUnitalSubring_injective :
    Function.Injective (NonUnitalSubalgebra.toNonUnitalSubring : NonUnitalSubalgebra R A → NonUnitalSubring A) := fun S T h => NonUnitalSubalgebra.ext fun x => by rw [← NonUnitalSubalgebra.mem_toNonUnitalSubring, ← NonUnitalSubalgebra.mem_toNonUnitalSubring, h]

