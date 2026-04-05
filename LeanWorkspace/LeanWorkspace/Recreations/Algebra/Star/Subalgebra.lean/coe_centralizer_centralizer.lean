import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

variable (S : StarSubalgebra R A)

theorem coe_centralizer_centralizer (s : Set A) :
    (StarSubalgebra.centralizer R (StarSubalgebra.centralizer R s : Set A)) = (s ∪ star s).centralizer.centralizer := by
  rw [StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq, Set.union_self, StarSubalgebra.coe_centralizer]

