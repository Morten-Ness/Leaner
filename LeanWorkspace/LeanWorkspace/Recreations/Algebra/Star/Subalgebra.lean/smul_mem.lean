import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

variable (S : StarSubalgebra R A)

theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S := (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem r) hx

