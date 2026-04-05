import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

theorem toSubalgebra_injective :
    Function.Injective (toSubalgebra : StarSubalgebra R A → Subalgebra R A) := fun S T h =>
  StarSubalgebra.ext fun x => by rw [← StarSubalgebra.mem_toSubalgebra, ← StarSubalgebra.mem_toSubalgebra, h]

